import ReactorModel.Objects.Reactor.ReactorType.WellFounded

noncomputable section
open Classical
open Reactor (Component)

namespace ReactorType

variable [ReactorType α] [ReactorType β] in section

-- TODO: Find a better name for this.
def RootEqualUpTo (cpt : Component) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cpt ∨ j ≠ i) → cpt? c rtr₁ j = cpt? c rtr₂ j

theorem RootEqualUpTo.mem_iff {rtr₁ : α} (e : RootEqualUpTo cpt i rtr₁ rtr₂) 
    (h : c ≠ cpt ∨ j ≠ i) : (j ∈ cpt? c rtr₁) ↔ (j ∈ cpt? c rtr₂) := by
  simp [Partial.mem_iff]
  exact ⟨(e h ▸ ·), (e h ▸ ·)⟩   

-- Note: Without ID-uniqueness this can be satisfied by updating exactly one of the occurrences of
--       the target. Since we have a choice of which target we update, this type isn't a `Prop`. 
--       (We need to be able to eliminate into `Type` in `Member.fromLawfulUpdate`).
inductive LawfulMemUpdate (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) : α → α → Type
  | final : 
    (RootEqualUpTo cpt i rtr₁ rtr₂) → (cpt? cpt rtr₁ i = some o) → (cpt? cpt rtr₂ i = f o) → 
    LawfulMemUpdate cpt i f rtr₁ rtr₂
  | nest : 
    (RootEqualUpTo .rtr j rtr₁ rtr₂) → (cpt? .rtr rtr₁ j = some n₁) → (cpt? .rtr rtr₂ j = some n₂) → 
    (LawfulMemUpdate cpt i f n₁ n₂) → LawfulMemUpdate cpt i f rtr₁ rtr₂

-- Note: This isn't a `Prop` because of the explanation on `LawfulMemUpdate`.
inductive LawfulUpdate (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) (rtr₁ rtr₂ : α)
  | update (u : LawfulMemUpdate cpt i f rtr₁ rtr₂)
  | notMem (h : IsEmpty $ Member cpt i rtr₁) (eq : rtr₁ = rtr₂)

theorem RootEqualUpTo.lift [l : LawfulCoe α β] {rtr₁ rtr₂ : α} 
    (e : RootEqualUpTo cpt i (rtr₁ : β) (rtr₂ : β)) : RootEqualUpTo cpt i rtr₁ rtr₂ := by
  intro c j h
  have he := e h
  cases h₁ : cpt? c (rtr₁ : β) j <;> cases h₂ : cpt? c (rtr₂ : β) j <;> simp_all
  case none.none => simp [l.lift_cpt?_eq_none _ h₁, l.lift_cpt?_eq_none _ h₂]
  case some.some => 
    cases c <;> try cases ‹Reactor.Component.Valued› 
    all_goals try simp [l.lift_cpt?_eq_some _ h₁, l.lift_cpt?_eq_some _ h₂]
    case rtr =>
      have ⟨_, _, h₁'⟩ := l.lift_nest_eq_some h₁
      have ⟨_, _, h₂'⟩ := l.lift_nest_eq_some h₂
      subst h₁'
      simp [l.lift_cpt?_eq_some _ h₁, l.lift_cpt?_eq_some _ h₂]

def LawfulMemUpdate.lift [c : LawfulCoe α β] {rtr₁ rtr₂ : α} :
    (LawfulMemUpdate cpt i f (rtr₁ : β) (rtr₂ : β)) → LawfulMemUpdate cpt i f rtr₁ rtr₂
  | final e h₁ h₂ (o := o) => 
    have h₁ : cpt? cpt rtr₁ i = some o     := by cases cpt <;> exact c.lift_cpt?_eq_some _ h₁
    have h₂ : cpt? cpt rtr₂ i = some (f o) := by cases cpt <;> exact c.lift_cpt?_eq_some _ h₂
    .final e.lift h₁ h₂
  | nest (n₁ := n₁) (n₂ := n₂) e h₁ h₂ u (j := j) => 
    have o₁ := c.lift_nest_eq_some h₁
    have o₂ := c.lift_nest_eq_some h₂
    have ⟨h₁, h₁'⟩ := o₁.choose_spec
    have ⟨h₂, h₂'⟩ := o₂.choose_spec 
    let u' : LawfulMemUpdate cpt i f (o₁.choose : β) (o₂.choose : β) := cast (by simp [h₁', h₂']) u
    .nest e.lift h₁ h₂ u'.lift
termination_by lift u => sizeOf u
decreasing_by simp_wf; have h : sizeOf u' = sizeOf u := (by congr; apply cast_heq); simp [h]

-- TODO:
-- If we consider the following following diagram:
-- 
--     rtr₁ -u.lift→ rtr₂
--      |             |
--     coe           coe
--      ↓             ↓
-- (rtr₁ : β) -u→ (rtr₂ : β)
--
-- ... there's something functorial about this. The `lift` looks like a functor's `map` over `u`.
-- Figure out if there's a way of modelling some part of this as a functor. 
def LawfulUpdate.lift [c : LawfulCoe α β] {rtr₁ rtr₂ : α} :
    (LawfulUpdate cpt i f (rtr₁ : β) (rtr₂ : β)) → LawfulUpdate cpt i f rtr₁ rtr₂
  | update u => update u.lift
  | notMem h eq =>  
    let u := notMem (byContradiction (h.false $ not_isEmpty_iff.mp · |>.some.fromLawfulCoe)) rfl
    (c.inj eq) ▸ u 

end

class Updatable (α) extends ReactorType.WellFounded α where
  update : α → (cpt : Component.Valued) → ID → (cpt.type → cpt.type) → α  
    
class LawfulUpdatable (α) extends Updatable α where 
  lawful : ∀ rtr cpt i f, LawfulUpdate cpt i f rtr (update rtr cpt i f)      

scoped macro "lawfulUpdatableCoe_update_coe_comm_proof" : tactic =>
  `(tactic| simp [Updatable.update, Coe.coe])

class LawfulUpdatableCoe (α β) [a : Updatable α] [b : Updatable β] extends LawfulCoe α β where
  update_coe_comm : 
    ∀ {rtr cpt i f}, b.update (coe rtr) cpt i f = coe (a.update rtr cpt i f) := by 
      lawfulUpdatableCoe_update_coe_comm_proof

instance [Updatable α] [LawfulUpdatable β] [c : LawfulUpdatableCoe α β] : LawfulUpdatable α where
  lawful rtr cpt i f := c.update_coe_comm ▸ LawfulUpdatable.lawful (rtr : β) cpt i f |>.lift 

end ReactorType