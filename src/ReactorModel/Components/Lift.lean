import ReactorModel.Components.Reaction

variable {ι υ} [ID ι] [Value υ]

namespace Reactor 

def fromRaw {raw : Raw.Reactor ι υ} (h : raw.wellFormed) : Reactor ι υ :=
  { raw := raw, rawWF := h }

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

theorem rawEquiv_mutates_iff {c : Change ι υ} {raw : Raw.Change ι υ} (h : c.rawEquiv raw) :
  c.mutates ↔ raw.mutates := by
  simp [mutates, Raw.Change.mutates]
  cases h
  case port h₁ h₂ =>       simp [h₁, h₂]
  case state h₁ h₂ =>      simp [h₁, h₂]
  case connect h₁ h₂ =>    simp [h₁, h₂]
  case disconnect h₁ h₂ => simp [h₁, h₂]
  case delete h₁ h₂ =>     simp [h₁, h₂]
  case create h₁ h₂ _ =>   simp [h₁, h₂]

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
    cases Change.fromRaw_rawEquiv he
    case port hp he' =>
      injection hp with ht hv
      rw [he', ←ht, ←hv] at hc
      contradiction
    all_goals { contradiction },
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
    have h := Change.fromRaw_rawEquiv (Eq.refl $ Change.fromRaw hw hr hc)
    exact mt (Change.rawEquiv_mutates_iff h).mpr ha
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

theorem fromRaw_rawEquiv {rcn : Reaction ι υ} {rtr raw hw hr} :
  rcn = @Reaction.fromRaw _ _ _ _ rtr hw raw hr → rcn.rawEquiv raw := 
  λ h => {
    deps := by simp [h, fromRaw],
    triggers := by simp [h, fromRaw],
    children := by simp [h, fromRaw],
    body := by
      intro p s
      simp [fromRaw] at h
      simp [Reaction.ext_iff] at h
      have h := h.right.right.right
      have h : rcn.body p s = (raw.body p s).attach.map (λ c => Change.fromRaw hw hr _) := by rw [h]
      generalize hl : rcn p s = l
      rw [hl] at h
      induction l
      case nil =>
        have h := List.map_eq_nil.mp (Eq.symm h)
        simp at h
        rw [h]
        exact List.forall₂.nil
      case cons hd tl hi =>
        -- something's weird with hi here  
        cases hc : List.attach (raw.body p s)
        case nil =>
          rw [hc, List.map_nil] at h
          contradiction
        case cons hd' tl' =>
          simp [hc] at h
          cases hc' : raw.body p s
          case nil =>
            simp [hc'] at hc
            sorry
          sorry
  }

theorem rawEquiv_isMut_iff {rcn : Reaction ι υ} {raw : Raw.Reaction ι υ} (h : rcn.rawEquiv raw) :
  rcn.isMut → raw.isMut := by
  intro hm
  simp [Raw.Reaction.isMut, Raw.Reaction.isNorm]
  simp [isMut, isNorm] at hm
  obtain ⟨p, s, c, h₁, h₂⟩ := hm
  exists p
  exists s
  have h := h.body p s
  rw [List.forall₂_iff] at h
  cases h
  case inl h =>
    rw [h.left] at h₁
    contradiction
  case inr h =>
    obtain ⟨a, b, l₁, l₂, hc, hl, hw₁, hw₂⟩ := h
    have H := Change.rawEquiv_mutates_iff hc
    sorry
    -- somehow l₁ and l₂ and hence a b are disconnected from h₁ and h₂

end Reaction
