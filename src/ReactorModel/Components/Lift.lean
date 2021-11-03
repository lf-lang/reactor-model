import ReactorModel.Components.Reaction

variable {ι υ} [ID ι] [Value υ]

namespace Reactor 

def fromRaw {raw : Raw.Reactor ι υ} (h : raw.wellFormed) : Reactor ι υ :=
  { raw := raw, wf := h }

def rawEquiv (rtr : Reactor ι υ) (raw : Raw.Reactor ι υ) : Prop :=
  rtr.raw = raw

theorem fromRaw_rawEquiv {rtr : Reactor ι υ} {raw h} : 
  rtr = Reactor.fromRaw (raw := raw) h → rtr.rawEquiv raw :=
  λ h => by simp [fromRaw, rawEquiv, h]

end Reactor

namespace Change

-- If we have a well-formed raw reactor `rtr` which contains a raw reaction `rcn`
-- which can produce a raw change `c`, then we can convert that raw change to a
-- "proper" change.
--
-- This conversion is trivial for all changes except `Change.create`, where we
-- have to turn a raw reactor into a "proper" reactor. That's why we need all
-- the auxiliary proofs as input.
def fromRaw
  {rtr : Raw.Reactor ι υ} (hw : rtr.wellFormed) 
  {rcn : Raw.Reaction ι υ} (hr : ∃ i, rtr.rcns i = rcn) 
  {raw : Raw.Change ι υ} {p s} (hc : raw ∈ Raw.Reaction.body rcn p s) : 
  Change ι υ :=
  match hm:raw with 
    | Raw.Change.port target value  => Change.port target value  
    | Raw.Change.state target value => Change.state target value 
    | Raw.Change.connect src dst    => Change.connect src dst    
    | Raw.Change.disconnect src dst => Change.disconnect src dst 
    | Raw.Change.delete rtrID       => Change.delete rtrID
    | Raw.Change.create cr id => 
      let cr' := Reactor.fromRaw (by
          rw [hm] at hc
          have ha := Raw.Reactor.isAncestorOf.creatable hr.choose_spec hc
          exact Raw.Reactor.isAncestorOf_preserves_wf ha hw
      )
      Change.create cr' id

-- To ensure that `Change.fromRaw` performs a sensible transformation from
-- raw to "proper" changes, we define what it means for a raw and a "proper"
-- changes to be "equivalent" (they contain the same data).
-- This notion of equivalence is then used in `Change.fromRaw_equiv_to_raw` to
-- prove that `Change.fromRaw` produces only equivalent changes.
inductive rawEquiv (c : Change ι υ) (raw : Raw.Change ι υ) : Prop
  | port       {t v} :    (c = Change.port t v)       → (raw = Raw.Change.port t v)                         → rawEquiv c raw
  | state      {t v} :    (c = Change.state t v)      → (raw = Raw.Change.state t v)                        → rawEquiv c raw
  | connect    {s d} :    (c = Change.connect s d)    → (raw = Raw.Change.connect s d)                      → rawEquiv c raw
  | disconnect {s d} :    (c = Change.disconnect s d) → (raw = Raw.Change.disconnect s d)                   → rawEquiv c raw
  | create     {r r' i} : (c = Change.create r i)     → (raw = Raw.Change.create r' i)    → (r.rawEquiv r') → rawEquiv c raw
  | delete     {i}   :    (c = Change.delete i)       → (raw = Raw.Change.delete i)                         → rawEquiv c raw

theorem fromRaw_rawEquiv {c : Change ι υ} {rtr rcn raw p s hw hr hc} :
  c = @Change.fromRaw _ _ _ _ rtr hw rcn hr raw p s hc → c.rawEquiv raw := by
  intro h
  cases raw
  case port t v =>
    cases c
    case port =>
      apply rawEquiv.port (t := t) (v := v)
      all_goals { simp [fromRaw, h] }
    all_goals { simp [fromRaw] at h }
  case state t v =>
    cases c
    case state =>
      apply rawEquiv.state (t := t) (v := v)
      all_goals { simp [fromRaw, h] }
    all_goals { simp [fromRaw] at h }
  case connect s d =>
    cases c
    case connect =>
      apply rawEquiv.connect (s := s) (d := d)
      all_goals { simp [fromRaw, h] }
    all_goals { simp [fromRaw] at h }
  case disconnect s d =>
    cases c
    case disconnect =>
      apply rawEquiv.disconnect (s := s) (d := d)
      all_goals { simp [fromRaw, h] }
    all_goals { simp [fromRaw] at h }
  case delete i =>
    cases c
    case delete =>
      apply rawEquiv.delete (i := i)
      all_goals { simp [fromRaw, h] }
    all_goals { simp [fromRaw] at h }
  case create r' i' =>
    cases c
    case create r i =>
      apply rawEquiv.create (r := r) (r' := r') (i := i)
      simp
      focus
        simp [fromRaw] at h
        simp [h]
      focus
        simp [fromRaw] at h
        exact Reactor.fromRaw_rawEquiv h.left
    all_goals { simp [fromRaw] at h }
  
-- If a given `Change.port i v` was obtained from a raw change via
-- `fromRaw`, then that original raw change was a `Raw.Change.port i v`.
-- That is, `fromRaw` maintains the kind of change.
--
-- Note, this proof could be generalized to all kinds of changes,
-- but it's only needed for `Reactor.rcns` > `outDepOnly` so we
-- only show it for `Change.port`.
--
-- TODO: This should be a direct consequence of `rawEquiv`.
theorem fromRaw_same_change_port 
  {rtr : Raw.Reactor ι υ} {hw : rtr.wellFormed}
  {rcn : Raw.Reaction ι υ} {hr : ∃ i, rtr.rcns i = rcn}
  {c : Raw.Change ι υ} {p s} {hc : c ∈ Raw.Reaction.body rcn p s} 
  {i : ι} {v : υ} :
  Change.port i v = Change.fromRaw hw hr hc → c = Raw.Change.port i v := by
  intro h
  simp only [fromRaw] at h
  cases c
  case port =>
    simp at h
    simp [h]
  all_goals { simp at h }

-- If a given mutating change (cf. `mutates`) was obtained from a
-- raw change via `fromRaw`, then that original raw change must also
-- have been mutating.
-- That is, `fromRaw` maintains "mutatingness".
--
-- TODO: This might be a trivial consequence of `rawEquiv`.
theorem fromRaw_same_mutates 
  {rtr : Raw.Reactor ι υ} {hw : rtr.wellFormed}
  {rcn : Raw.Reaction ι υ} {hr : ∃ i, rtr.rcns i = rcn}
  {c : Raw.Change ι υ} {p s} {hc : c ∈ Raw.Reaction.body rcn p s} :
  c.mutates → (Change.fromRaw hw hr hc).mutates := by
  intro h
  simp only [fromRaw]
  cases c
  all_goals { simp; assumption }

end Change

namespace Reaction

def fromRaw {rtr : Raw.Reactor ι υ} (hw : rtr.wellFormed) {raw : Raw.Reaction ι υ} (hr : ∃ i, rtr.rcns i = raw) : Reaction ι υ := {
  deps := raw.deps,
  triggers := raw.triggers,
  children := raw.children,
  body := (λ p s => (raw.body p s).attach.map (λ c => Change.fromRaw hw hr c.property)),
  tsSubInDeps := (hw.direct.rcnsWF hr).tsSubInDeps,
  outDepOnly := by
    intro p s _ v ho hc
    simp [List.mem_map] at hc
    obtain ⟨c, hc, he⟩ := hc
    have hw := (hw.direct.rcnsWF hr).outDepOnly p s v ho
    have hp := Change.fromRaw_same_change_port he
    rw [hp] at hc
    contradiction
  ,
  normNoChild := by
    intro ha
    have hn := (hw.direct.rcnsWF hr).normNoChild
    simp at ha
    simp [Raw.Reaction.isNorm] at hw
    suffices hg : ∀ i s c, c ∈ raw.body i s → ¬c.mutates from hn hg
    intro i s c hc
    have ha := ha i s (Change.fromRaw hw hr hc)
    simp only [List.mem_map] at ha
    have ha := ha (by
      let a : { x // x ∈ raw.body i s } := ⟨c, hc⟩
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

theorem fromRaw_rawEquiv (rcn : Reaction ι υ) {rtr raw hw hr} :
  rcn = @Reaction.fromRaw _ _ _ _ rtr hw raw hr → rcn.rawEquiv raw := 
  λ h => {
    deps := by simp [h, fromRaw],
    triggers := by simp [h, fromRaw],
    children := by simp [h, fromRaw],
    body := by
      intro p s
      -- induction on (rcn p s) and (raw.body p s)?
      sorry
  }

end Reaction
