import ReactorModel.Components.Reaction

variable {ι υ} [Value υ]

namespace Reactor 

-- `Reactor.fromRaw` is already defined as the name of `Reactor`'s constructor.

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
  {raw : Raw.Change ι υ} {i} (hc : raw ∈ rcn.body i) : 
  Change ι υ :=
  match hm:raw with 
    | Raw.Change.port target value        => Change.port target value  
    | Raw.Change.state target value       => Change.state target value 
    | Raw.Change.action target time value => Change.action target time value 
    | Raw.Change.connect src dst          => Change.connect src dst    
    | Raw.Change.disconnect src dst       => Change.disconnect src dst 
    | Raw.Change.delete rtrID             => Change.delete rtrID
    | Raw.Change.create cr id => 
      let cr' := Reactor.fromRaw _ (by
          rw [hm] at hc
          have ha := Raw.Reactor.isAncestorOf.creatable hr.choose_spec hc
          exact Raw.Reactor.isAncestorOf_preserves_wf ha hw
      )
      Change.create cr' id

-- To ensure that `Change.fromRaw` performs a sensible transformation from
-- raw to "proper" changes, we define what it means for raw and "proper"
-- changes to be "equivalent" (they contain the same data).
-- This notion of equivalence is then used in `Change.fromRaw_rawEquiv` to
-- prove that `Change.fromRaw` produces only equivalent changes.
inductive rawEquiv : Change ι υ → Raw.Change ι υ → Prop
  | port       {t v} :                      rawEquiv (Change.port t v) (Raw.Change.port t v)
  | state      {t v} :                      rawEquiv (Change.state t v) (Raw.Change.state t v)
  | action     {t tm v} :                   rawEquiv (Change.action t tm v) (Raw.Change.action t tm v)
  | connect    {s d} :                      rawEquiv (Change.connect s d) (Raw.Change.connect s d)
  | disconnect {s d} :                      rawEquiv (Change.disconnect s d) (Raw.Change.disconnect s d)
  | create     {r r' i} : (r.rawEquiv r') → rawEquiv (Change.create r i) (Raw.Change.create r' i)
  | delete     {i} :                        rawEquiv (Change.delete i) (Raw.Change.delete i)

theorem fromRaw_rawEquiv {c : Change ι υ} {rtr rcn raw i hw hr hc} :
  c = @Change.fromRaw _ _ _ rtr hw rcn hr raw i hc → c.rawEquiv raw := by
  intro h
  cases raw <;> cases c <;> simp [fromRaw] at h
  case port.port =>             simp [h, rawEquiv.port]
  case state.state =>           simp [h, rawEquiv.state]
  case action.action =>         simp [h, rawEquiv.action]
  case connect.connect =>       simp [h, rawEquiv.connect]
  case disconnect.disconnect => simp [h, rawEquiv.disconnect]
  case delete.delete =>         simp [h, rawEquiv.delete]
  case create.create r i => rw [h.right]; exact rawEquiv.create $ Reactor.fromRaw_rawEquiv h.left

theorem rawEquiv_mutates_iff {c : Change ι υ} {raw : Raw.Change ι υ} (h : c.rawEquiv raw) :
  c.mutates ↔ raw.mutates := by
  cases h <;> simp [mutates, Raw.Change.mutates]

end Change

namespace Reaction

-- If we have a well-formed raw reactor `rtr` which contains a raw reaction `rcn`,
-- then we can convert that raw reaction to a "proper" reaction.
-- In the process we map all raw changes producable by the raw reaction to "proper"
-- changes (using `Change.fromRaw`).
def fromRaw {rtr : Raw.Reactor ι υ} (hw : rtr.wellFormed) {raw : Raw.Reaction ι υ} (hr : ∃ i, rtr.rcns i = raw) : Reaction ι υ := {
  deps := raw.deps,
  triggers := raw.triggers,
  children := raw.children,
  body := (λ i => (raw.body i).attach.map (λ c => Change.fromRaw hw hr c.property)),
  tsSubInDeps := (hw.direct.rcnsWF hr).tsSubInDeps,
  prtOutDepOnly := by
    intro i _ v ho hc
    simp [List.mem_map] at hc
    have hw := (hw.direct.rcnsWF hr).prtOutDepOnly i v ho
    obtain ⟨_, _, he⟩ := hc
    cases Change.fromRaw_rawEquiv he
    contradiction,
  actOutDepOnly := by
    intro i _ t v ho hc
    simp [List.mem_map] at hc
    have hw := (hw.direct.rcnsWF hr).actOutDepOnly i t v ho
    obtain ⟨_, _, he⟩ := hc
    cases Change.fromRaw_rawEquiv he
    contradiction,
  normNoChild := by
    intro ha
    have hn := (hw.direct.rcnsWF hr).normNoChild
    simp at ha
    simp [Raw.Reaction.isNorm] at hw
    suffices hg : ∀ i c, c ∈ raw.body i → ¬c.mutates from hn hg
    intro i c hc
    have ha := ha i (Change.fromRaw hw hr hc)
    simp only [List.mem_map] at ha
    have ha := ha (by
      let a : { x // x ∈ raw.body i } := ⟨c, hc⟩
      exists a
      simp [List.mem_attach]
    )
    have h := Change.fromRaw_rawEquiv (Eq.refl $ Change.fromRaw hw hr hc)
    exact mt (Change.rawEquiv_mutates_iff h).mpr ha
}

-- To ensure that `fromRaw` performs a sensible transformation from a raw
-- to a "proper" reaction, we define what it means for raw and "proper"
-- reactions to be "equivalent" (they contain the same data).
-- This notion of equivalence is then used in `fromRaw_rawEquiv` to
-- prove that `fromRaw` produces only equivalent reactions.
structure rawEquiv (rcn : Reaction ι υ) (raw : Raw.Reaction ι υ) : Prop :=
  deps :     rcn.deps = raw.deps
  triggers : rcn.triggers = raw.triggers
  children : rcn.children = raw.children
  body :     ∀ i, List.forall₂ Change.rawEquiv (rcn.body i) (raw.body i)

theorem fromRaw_rawEquiv {rcn : Reaction ι υ} {rtr raw hw hr} :
  rcn = @Reaction.fromRaw _ _ _ rtr hw raw hr → rcn.rawEquiv raw := 
  λ h => {
    deps := by simp [h, fromRaw],
    triggers := by simp [h, fromRaw],
    children := by simp [h, fromRaw],
    body := by
      intro i
      simp [fromRaw] at h
      simp [Reaction.ext_iff] at h
      have h := h.right.right.right
      have h : rcn.body i = (raw.body i).attach.map (λ c => Change.fromRaw hw hr _) := by rw [h]
      generalize hl : rcn i = l
      rw [hl] at h
      induction l
      case nil =>
        have h := List.map_eq_nil.mp (Eq.symm h)
        simp at h
        rw [h]
        exact List.forall₂.nil
      case cons hd tl hi =>
        -- something's weird with hi here  
        cases hc : List.attach (raw.body i)
        case nil =>
          rw [hc, List.map_nil] at h
          contradiction
        case cons hd' tl' =>
          simp [hc] at h
          cases hc' : raw.body i
          case nil =>
            simp [hc'] at hc
            sorry
          sorry
  }

theorem rawEquiv_isMut_iff {rcn : Reaction ι υ} {raw : Raw.Reaction ι υ} (h : rcn.rawEquiv raw) :
  rcn.isMut ↔ raw.isMut := by
  apply Iff.intro
  intro hm
  simp [Raw.Reaction.isMut, Raw.Reaction.isNorm]
  simp [isMut, isNorm] at hm
  obtain ⟨i, c, h₁, h₂⟩ := hm
  exists i
  have h := h.body i
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
  sorry

theorem rawEquiv_isNorm_iff {rcn : Reaction ι υ} {raw : Raw.Reaction ι υ} (h : rcn.rawEquiv raw) :
  rcn.isNorm ↔ raw.isNorm := by
  have he := rawEquiv_isMut_iff h
  simp only [isMut, Raw.Reaction.isMut] at he
  have he := not_iff_not_of_iff he
  simp at he
  exact he

end Reaction
