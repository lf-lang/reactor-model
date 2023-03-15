import ReactorModel.Objects.Reactor.ReactorType.Updatable

open Classical

namespace Reactor

protected inductive Core 
  | mk 
    (ports : Kind → ID ⇀ Value)
    (acts :  ID ⇀ Time.Tag ⇉ Value)
    (state : ID ⇀ Value)
    (rcns :  ID ⇀ Reaction)
    (nest :  ID → Option Reactor.Core)

namespace Core

instance reactorType : ReactorType Reactor.Core where
  ports | mk p _ _ _ _ => p
  acts  | mk _ a _ _ _ => a
  state | mk _ _ s _ _ => s 
  rcns  | mk _ _ _ r _ => r
  nest  | mk _ _ _ _ n => n

instance : ReactorType.Extensional Reactor.Core where
  ext_iff := by intro (mk ..) (mk ..); open ReactorType in simp [ports, state, rcns, acts, nest]

noncomputable section Update
open ReactorType

abbrev «with» 
    (rtr : Reactor.Core) (ports : Kind → ID ⇀ Value := ports rtr) 
    (acts : ID ⇀ Time.Tag ⇉ Value := acts rtr) (state : ID ⇀ Value := state rtr) 
    (rcns : ID ⇀ Reaction := rcns rtr) (nest : ID ⇀ Reactor.Core := nest rtr) :=
  Reactor.Core.mk ports acts state rcns nest

def insert [inst : ReactorType Reactor.Core] 
    (rtr : Reactor.Core) (cmp : Component) (i : ID) (v : inst.componentType cmp) :=
  match cmp with
  | .prt k => rtr.with (ports := Function.update (ports rtr) k $ ports rtr k |>.insert i v)
  | .act   => rtr.with (acts  := acts  rtr |>.insert i v)
  | .stv   => rtr.with (state := state rtr |>.insert i v)
  | .rcn   => rtr.with (rcns  := rcns  rtr |>.insert i v)
  | .rtr   => rtr.with (nest  := nest  rtr |>.insert i v)

theorem insert_cmp?_eq_self {rtr : Reactor.Core} (cmp) {i v} : 
    cmp? cmp (rtr.insert cmp i v) i = v := by
  cases cmp <;> try cases ‹Component.Valued› 
  all_goals
    simp [insert, cmp?, reactorType]
    apply Partial.insert_same

theorem insert_cmp?_ne_cmp_or_id {rtr : Reactor.Core} {cmp v} (h : c ≠ cmp ∨ j ≠ i) :
    cmp? c rtr j = cmp? c (rtr.insert cmp i v) j := by
  cases cmp <;> try cases ‹Component.Valued› <;> try cases ‹Kind›
  all_goals cases c <;> try cases ‹Component.Valued› <;> try cases ‹Kind›
  all_goals 
    simp [cmp?, insert]
    try simp [reactorType]; done
  all_goals
    cases h
    case inl h => contradiction
    case inr h => exact Partial.insert_ne _ h |>.symm

def updateMem {rtr : Reactor.Core} {cmp : Component.Valued} (f : cmp.type → cmp.type) : 
    Member cmp i rtr → Reactor.Core
  | .final h           => rtr.insert cmp i $ f (Partial.mem_ids_iff.mp h).choose
  | .nest (j := j) _ l => rtr.insert .rtr j (updateMem f l)

theorem updateMem_lawfulMemUpdate 
    {cmp : Component.Valued} (l : Member cmp i rtr) 
    (f : cmp.type → cmp.type) : LawfulMemUpdate cmp i f rtr (updateMem f l) := by
  induction l <;> simp [updateMem] 
  case final h =>
    replace h := Partial.mem_ids_iff.mp h
    exact .final insert_cmp?_ne_cmp_or_id h.choose_spec (insert_cmp?_eq_self cmp)
  case nest h l hi =>
    exact .nest insert_cmp?_ne_cmp_or_id h (insert_cmp?_eq_self .rtr) hi

def update (rtr : Reactor.Core) (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) :=
  if l : Nonempty (Member cmp i rtr) then updateMem f l.some else rtr

instance : ReactorType.LawfulUpdatable Reactor.Core where
  update := update
  lawful rtr cmp i f := by
    simp [update]
    split
    case inr h => simp at h; exact .notMem h
    case inl h => exact .update $ updateMem_lawfulMemUpdate h.some f

end Update
end Core
end Reactor