import ReactorModel.Components.Change

open Ports
open Classical

variable (ι υ) [ID ι] [Value υ]

structure Reaction where
  deps :        Ports.Role → Finset ι 
  triggers :    Finset ι
  children :    Finset ι
  body :        Ports ι υ → StateVars ι υ → List (Change ι υ)
  tsSubInDeps : triggers ⊆ deps Role.in
  outDepOnly :  ∀ p s {o} (v : υ), (o ∉ deps Role.out) → (Change.port o v) ∉ (body p s)
  normNoChild : (∀ i s c, c ∈ (body i s) → ¬c.mutates) → children = ∅

variable {ι υ}

namespace Reaction

-- A coercion so that reactions can be called directly as functions.
instance : CoeFun (Reaction ι υ) (λ _ => Ports ι υ → StateVars ι υ → (List (Change ι υ))) where
  coe rcn := rcn.body

-- A reaction is normal ("norm") if its body produces no mutating changes.
def isNorm (rcn : Reaction ι υ) : Prop :=
  ∀ i s c, c ∈ (rcn i s) → ¬c.mutates

def isMut (rcn : Reaction ι υ) : Prop := ¬rcn.isNorm

theorem norm_no_child' (rcn : Reaction ι υ) : rcn.isNorm → rcn.children = ∅ := 
  rcn.normNoChild

-- A relay reaction that connects a `src` port with a `dst` port.
def relay (src dst : ι) : Reaction ι υ := {
  deps := λ r => match r with | Role.in => Finset.singleton src | Role.out => Finset.singleton dst,
  triggers := Finset.singleton src,
  children := ∅,
  body := λ p _ => match p[src] with | none => [] | some v => [Change.port dst v],
  tsSubInDeps := by simp,
  outDepOnly := by
    intro p _ o v h hc
    simp at *
    cases hs : p[src]
    case none => simp [hs] at *
    case some v' =>
      simp [hs] at *
      rw [Finset.not_mem_singleton] at h
      have hc' := hc.left
      contradiction
  normNoChild := by simp
}

noncomputable def updateInDeps {rcn : Reaction ι υ} {is : Finset ι} : Reaction ι υ := 
  let deps' := Function.update rcn.deps Role.in is
  {
    deps := deps',
    triggers := rcn.triggers ∩ (deps' Role.in), 
    children := rcn.children,
    body := rcn.body,
    tsSubInDeps := Finset.inter_subset_right _ _,
    outDepOnly := λ i s _ v h' => rcn.outDepOnly i s v h',
    normNoChild := rcn.normNoChild
  }

noncomputable def updateOutDeps {rcn : Reaction ι υ} {is : Finset ι} (h : ∀ i s {o} (v : υ), (o ∉ is) → (Change.port o v) ∉ rcn i s) : Reaction ι υ := 
  let deps' := Function.update rcn.deps Role.out is
  {
    deps := deps',
    triggers := rcn.triggers ∩ (deps' Role.in), 
    children := rcn.children,
    body := rcn.body,
    tsSubInDeps := Finset.inter_subset_right _ _,
    outDepOnly := λ i s _ v h' => h i s v h',
    normNoChild := rcn.normNoChild
  } 

noncomputable def updateTriggers {rcn : Reaction ι υ} {is : Finset ι} (h : is ⊆ rcn.deps Role.in) : Reaction ι υ := {
  deps := rcn.deps,
  triggers := is, 
  children := rcn.children,
  body := rcn.body,
  tsSubInDeps := h,
  outDepOnly := rcn.outDepOnly,
  normNoChild := rcn.normNoChild
}

noncomputable def updateChildren {rcn : Reaction ι υ} (is : Finset ι) (h : rcn.isMut) : Reaction ι υ := {
  deps := rcn.deps,
  triggers := rcn.triggers, 
  children := is,
  body := rcn.body,
  tsSubInDeps := rcn.tsSubInDeps,
  outDepOnly := rcn.outDepOnly,
  normNoChild := by
    simp only [isMut, isNorm] at h
    intro h'
    contradiction
}

-- The condition under which a given reaction triggers on a given (input) port-assignment.
def triggersOn (rcn : Reaction ι υ) (p : Ports ι υ) : Prop :=
  ∃ t, t ∈ rcn.triggers ∧ p[t] ≠ none

-- TODO: Shorten this proof when the `all_goals` tactic is more stable.
theorem eq_input_eq_triggering {rcn : Reaction ι υ} {p₁ p₂ : Ports ι υ} (h : p₁ =[rcn.deps Role.in] p₂) :
  rcn.triggersOn p₁ ↔ rcn.triggersOn p₂ := by
  simp [triggersOn, Ports.eqAt] at h ⊢
  apply Iff.intro
  case mp =>
    intro ⟨t, ⟨hm, hn⟩⟩
    exists t
    exists hm
    have ht := h _ $ Finset.subset_iff.mp rcn.tsSubInDeps hm
    simp [ht] at hn
    assumption
  case mpr =>
    intro ⟨t, ⟨hm, hn⟩⟩
    exists t
    exists hm
    have ht := h _ $ Finset.subset_iff.mp rcn.tsSubInDeps hm
    simp [←ht] at hn
    assumption

def fromRaw (raw : Raw.Reaction ι υ) (h : False) : Reaction ι υ := {
  deps := raw.deps,
  triggers := raw.triggers,
  children := raw.children,
  body := (λ p s => (raw.body p s).attach.map (λ c => Change.fromRaw rtr.wf h c.property)),
  tsSubInDeps := (rtr.wf.direct.rcnsWF h).tsSubInDeps,
  outDepOnly := by
    intro p s _ v ho hc
    simp [List.mem_map] at hc
    obtain ⟨c, hc, he⟩ := hc
    have hw := (rtr.wf.direct.rcnsWF h).outDepOnly p s v ho
    have hp := Change.fromRaw_same_change_port he
    simp at hp
    rw [hp] at hc
    contradiction
  ,
  normNoChild := by
    intro ha
    have hw := (rtr.wf.direct.rcnsWF h).normNoChild
    simp at ha
    simp [Raw.Reaction.isNorm] at hw
    suffices hg : ∀ i s c, c ∈ rcn.body i s → ¬c.mutates from hw hg
    intro i s c hc
    have ha := ha i s (Change.fromRaw rtr.wf h hc)
    simp only [List.mem_map] at ha
    have ha := ha (by
      let a : { x // x ∈ rcn.body i s } := ⟨c, hc⟩
      exists a
      simp [List.mem_attach]
    )
    exact (mt Change.fromRaw_same_mutates) ha
}

-- To ensure that `fromRaw` performs a sensible transformation from a raw
-- to a "proper" reaction, we define what it means for a raw and a "proper"
-- reaction to be "equivalent" (they contain the same data).
-- This notion of equivalence is then used in `fromRaw_rawEquiv` to
-- prove that `fromRaw` produces only equivalent reactions.
structure rawEquiv (rcn : Reaction ι υ) (raw : Raw.Reaction ι υ) : Prop :=
  deps :     rcn.deps = raw.deps
  triggers : rcn.triggers = raw.triggers
  children : rcn.children = raw.children
  body :     ∀ p s, List.forall₂ Change.rawEquiv (rcn.body p s) (raw.body p s)

theorem fromRaw_rawEquiv (rtr : Reactor ι υ) : False :=
  sorry

end Reaction

-- A non-`Raw` accessor for a `Reactor`'s mutations.
def Reactor.rcns (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  let raw : Finmap ι (Raw.Reaction ι υ) := { lookup := rtr.raw.rcns, finite := rtr.wf.direct.rcnsFinite }
  raw.map' (λ rcn h => 
    let h := (Finmap.values_def.mp h)
    Reaction.fromRaw rcn sorry
  )

noncomputable def Reactor.norms (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isNorm)

noncomputable def Reactor.muts (rtr : Reactor ι υ) : ι ▸ Reaction ι υ :=
  rtr.rcns.filter' (Reaction.isMut)  