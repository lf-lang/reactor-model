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
    
end Reaction