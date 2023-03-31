import ReactorModel.Objects.Reactor.ReactorType.Updatable

open Classical

namespace Reactor

protected inductive Core 
  | mk 
    (ports : Kind → ID ⇀ Value)
    (acts :  ID ⇀ Action)
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

instance : ReactorType.WellFounded Reactor.Core where
  wf := by
    constructor
    apply Reactor.Core.rec 
      (motive_1 := fun rtr => Acc ReactorType.Nested rtr) 
      (motive_2 := fun | none => True | some rtr => Acc ReactorType.Nested rtr)
    all_goals simp
    intro _ _ _ _ _ hi
    constructor
    intro n ⟨i, hn⟩
    simp [ReactorType.nest] at hn 
    have := hn ▸ hi i
    simp_all
    
noncomputable section Update
open ReactorType

abbrev «with» 
    (rtr : Reactor.Core) (ports : Kind → ID ⇀ Value := ports rtr) (acts : ID ⇀ Action := acts rtr) 
    (state : ID ⇀ Value := state rtr) (rcns : ID ⇀ Reaction := rcns rtr) 
    (nest : ID ⇀ Reactor.Core := nest rtr) :=
  Reactor.Core.mk ports acts state rcns nest

def insert [inst : ReactorType Reactor.Core] 
    (rtr : Reactor.Core) (cpt : Component) (i : ID) (v : inst.cptType cpt) :=
  match cpt with
  | .prt k => rtr.with (ports := Function.update (ports rtr) k $ ports rtr k |>.insert i v)
  | .act   => rtr.with (acts  := acts  rtr |>.insert i v)
  | .stv   => rtr.with (state := state rtr |>.insert i v)
  | .rcn   => rtr.with (rcns  := rcns  rtr |>.insert i v)
  | .rtr   => rtr.with (nest  := nest  rtr |>.insert i v)

theorem insert_cpt?_eq_self {rtr : Reactor.Core} (cpt) {i v} : 
    cpt? cpt (rtr.insert cpt i v) i = v := by
  cases cpt <;> try cases ‹Component.Valued› 
  all_goals
    simp [insert, cpt?, reactorType]
    apply Partial.insert_same

theorem insert_cpt?_ne_cpt_or_id {rtr : Reactor.Core} (h : c ≠ cpt ∨ j ≠ i) :
    cpt? c rtr j = cpt? c (rtr.insert cpt i v) j := by
  cases cpt <;> try cases ‹Component.Valued› <;> try cases ‹Kind›
  all_goals cases c <;> try cases ‹Component.Valued› <;> try cases ‹Kind›
  all_goals 
    simp [cpt?, insert]
    try simp [reactorType]; done
  all_goals
    cases h
    case inl h => contradiction
    case inr h => exact Partial.insert_ne _ h |>.symm

def updateMem {rtr : Reactor.Core} {cpt : Component.Valued} (f : cpt.type → cpt.type) : 
    Member cpt i rtr → Reactor.Core
  | .final h           => rtr.insert cpt i $ f (Partial.mem_iff.mp h).choose
  | .nest (j := j) _ l => rtr.insert .rtr j (updateMem f l)

theorem updateMem_lawfulMemUpdate 
    {cpt : Component.Valued} (l : Member cpt i rtr) 
    (f : cpt.type → cpt.type) : LawfulMemUpdate cpt i f rtr (updateMem f l) := by
  induction l <;> simp [updateMem] 
  case final h =>
    replace h := Partial.mem_iff.mp h
    exact .final insert_cpt?_ne_cpt_or_id h.choose_spec (insert_cpt?_eq_self cpt)
  case nest h l hi =>
    exact .nest insert_cpt?_ne_cpt_or_id h (insert_cpt?_eq_self .rtr) hi

def update (rtr : Reactor.Core) (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) :=
  if l : Nonempty (Member cpt i rtr) then updateMem f l.some else rtr

instance : ReactorType.LawfulUpdatable Reactor.Core where
  update := update
  lawful rtr cpt i f := 
    if h : Nonempty (Member (Component.val cpt) i rtr) 
    then .update $ by simp [update, h]; exact updateMem_lawfulMemUpdate h.some f
    else .notMem (not_nonempty_iff.mp h) $ by simp [update, h]

end Update
end Core
end Reactor