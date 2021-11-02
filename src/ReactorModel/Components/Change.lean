import ReactorModel.Components.Reactor

variable (ι υ) [ID ι] [Value υ]

inductive Change
  | port (target : ι) (value : υ)
  | state (target : ι) (value : υ)
  | connect (src : ι) (dst : ι)
  | disconnect (src : ι) (dst : ι)
  | create (rtr : Reactor ι υ) (id : ι)
  | delete (rtrID : ι)

variable {ι υ}

namespace Change

def mutates : Change ι υ → Bool 
  | port _ _       => false
  | state _ _      => false
  | connect _ _    => true
  | disconnect _ _ => true
  | create _ _     => true
  | delete _       => true

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
  {c : Raw.Change ι υ} {p s} (hc : c ∈ Raw.Reaction.body rcn p s) : 
  Change ι υ :=
  match hm:c with 
    | Raw.Change.port target value  => Change.port target value  
    | Raw.Change.state target value => Change.state target value 
    | Raw.Change.connect src dst    => Change.connect src dst    
    | Raw.Change.disconnect src dst => Change.disconnect src dst 
    | Raw.Change.delete rtrID       => Change.delete rtrID
    | Raw.Change.create cr id => 
      Change.create { 
        raw := cr, 
        wf := by 
          rw [hm] at hc
          have ha := Raw.Reactor.isAncestorOf.creatable hr.choose_spec hc
          exact Raw.Reactor.isAncestorOf_preserves_wf ha hw
      } id

-- If a given `Change.port i v` was obtained from a raw change via
-- `fromRaw`, then that original raw change was a `Raw.Change.port i v`.
-- That is, `fromRaw` maintains the kind of change.
--
-- Note, this proof could be generalized to all kinds of changes,
-- but it's only needed for `Reactor.rcns` > `outDepOnly` so we
-- only show it for `Change.port`.
--
-- TODO: This might be a direct consequence of `rawEquiv`.
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
  
theorem fromRaw_equiv_to_raw (c : Change ι υ) {rtr rcn raw p s hw hr hc} :
  c = @Change.fromRaw _ _ _ _ rtr hw rcn hr raw p s hc → c.rawEquiv raw :=
  sorry

end Change