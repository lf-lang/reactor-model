import ReactorModel.Objects.Reactor.ReactorType.WellFounded

noncomputable section
open Classical
open Reactor (Component)

namespace ReactorType

variable [ReactorType α] [ReactorType β] in section

-- TODO: Find a better name for this.
def RootEqualUpTo (cmp : Component) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cmp ∨ j ≠ i) → cmp? c rtr₁ j = cmp? c rtr₂ j

theorem RootEqualUpTo.mem_ids_iff {cmp} {rtr₁ : α} (e : RootEqualUpTo cmp i rtr₁ rtr₂) 
    (h : c ≠ cmp ∨ j ≠ i) : j ∈ (cmp? c rtr₁).ids ↔ j ∈ (cmp? c rtr₂).ids := by
  simp [Partial.mem_ids_iff]
  exact ⟨(e h ▸ ·), (e h ▸ ·)⟩   

-- Note: Without ID-uniqueness this can be satisfied by updating exactly one of the occurrences of
--       the target. Since we have a choice of which target we update, this type isn't a `Prop`. 
--       (We need to be able to eliminate into `Type` in `Member.fromLawfulUpdate`).
inductive LawfulMemUpdate (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) : α → α → Type
  | final : 
    (RootEqualUpTo cmp i rtr₁ rtr₂) → (cmp? cmp rtr₁ i = some o) → (cmp? cmp rtr₂ i = f o) → 
    LawfulMemUpdate cmp i f rtr₁ rtr₂
  | nest : 
    (RootEqualUpTo .rtr j rtr₁ rtr₂) → (cmp? .rtr rtr₁ j = some n₁) → (cmp? .rtr rtr₂ j = some n₂) → 
    (LawfulMemUpdate cmp i f n₁ n₂) → LawfulMemUpdate cmp i f rtr₁ rtr₂

-- Note: This isn't a `Prop` because of the explanation on `LawfulMemUpdate`.
inductive LawfulUpdate (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) (rtr₁ rtr₂ : α)
  | update (u : LawfulMemUpdate cmp i f rtr₁ rtr₂)
  | notMem (h : IsEmpty $ Member cmp i rtr₁) (eq : rtr₁ = rtr₂)

theorem RootEqualUpTo.lift [l : LawfulCoe α β] {cmp i} {rtr₁ rtr₂ : α} 
    (e : RootEqualUpTo cmp i (rtr₁ : β) (rtr₂ : β)) : RootEqualUpTo cmp i rtr₁ rtr₂ := by
  intro c j h
  have he := e h
  cases h₁ : cmp? c (rtr₁ : β) j <;> cases h₂ : cmp? c (rtr₂ : β) j <;> simp_all
  case none.none => simp [l.lift_cmp?_eq_none _ h₁, l.lift_cmp?_eq_none _ h₂]
  case some.some => 
    cases c <;> try cases ‹Reactor.Component.Valued› 
    all_goals try simp [l.lift_cmp?_eq_some _ h₁, l.lift_cmp?_eq_some _ h₂]
    case rtr =>
      have ⟨_, _, h₁'⟩ := l.lift_nest_eq_some h₁
      have ⟨_, _, h₂'⟩ := l.lift_nest_eq_some h₂
      subst h₁'
      simp [l.lift_cmp?_eq_some _ h₁, l.lift_cmp?_eq_some _ h₂]

def LawfulMemUpdate.lift [c : LawfulCoe α β] {rtr₁ rtr₂ : α} {cmp i f} :
    (LawfulMemUpdate cmp i f (rtr₁ : β) (rtr₂ : β)) → LawfulMemUpdate cmp i f rtr₁ rtr₂
  | final e h₁ h₂ (o := o) => 
    have h₁ : cmp? cmp rtr₁ i = some o     := by cases cmp <;> exact c.lift_cmp?_eq_some _ h₁
    have h₂ : cmp? cmp rtr₂ i = some (f o) := by cases cmp <;> exact c.lift_cmp?_eq_some _ h₂
    .final e.lift h₁ h₂
  | nest (n₁ := n₁) (n₂ := n₂) e h₁ h₂ u (j := j) => 
    have o₁ := c.lift_nest_eq_some h₁
    have o₂ := c.lift_nest_eq_some h₂
    have ⟨h₁, h₁'⟩ := o₁.choose_spec
    have ⟨h₂, h₂'⟩ := o₂.choose_spec 
    let u' : LawfulMemUpdate cmp i f (o₁.choose : β) (o₂.choose : β) := cast (by simp [h₁', h₂']) u
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
def LawfulUpdate.lift [c : LawfulCoe α β] {rtr₁ rtr₂ : α} {cmp i f} :
    (LawfulUpdate cmp i f (rtr₁ : β) (rtr₂ : β)) → LawfulUpdate cmp i f rtr₁ rtr₂
  | update u => update u.lift
  | notMem h eq =>  
    let u := notMem (byContradiction (h.false $ not_isEmpty_iff.mp · |>.some.fromLawfulCoe)) rfl
    (c.inj eq) ▸ u 

end

class Updatable (α) extends ReactorType.WellFounded α where
  update : α → (cmp : Component.Valued) → ID → (cmp.type → cmp.type) → α  
    
class LawfulUpdatable (α) extends Updatable α where 
  lawful : ∀ rtr cmp i f, LawfulUpdate cmp i f rtr (update rtr cmp i f)      

scoped macro "lawfulUpdatableCoe_update_coe_comm_proof" : tactic =>
  `(tactic| simp [Updatable.update, Coe.coe])

class LawfulUpdatableCoe (α β) [a : Updatable α] [b : Updatable β] extends LawfulCoe α β where
  update_coe_comm : 
    ∀ {rtr cmp i f}, b.update (coe rtr) cmp i f = coe (a.update rtr cmp i f) := by 
      lawfulUpdatableCoe_update_coe_comm_proof

instance [Updatable α] [LawfulUpdatable β] [c : LawfulUpdatableCoe α β] : LawfulUpdatable α where
  lawful rtr cmp i f := c.update_coe_comm ▸ LawfulUpdatable.lawful (rtr : β) cmp i f |>.lift 

end ReactorType