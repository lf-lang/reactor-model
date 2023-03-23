import ReactorModel.Objects.Reactor.ReactorType.WellFounded

open Reactor (Component)

namespace ReactorType

variable [ReactorType α] [ReactorType β] in section

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
inductive LawfulUpdate (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) : α → α → Type
  | update : (LawfulMemUpdate cmp i f rtr₁ rtr₂) → LawfulUpdate cmp i f rtr₁ rtr₂
  | notMem : (IsEmpty $ Member cmp i rtr)        → LawfulUpdate cmp i f rtr rtr

def LawfulUpdate.lift [LawfulCoe α β] {rtr₁ rtr₂ : α} {cmp i f} 
    (u : LawfulUpdate cmp i f (rtr₁ : β) (rtr₂ : β)) : LawfulUpdate cmp i f rtr₁ rtr₂ :=
  sorry -- might need coe ∘ update = update ∘ coe which is part of LawfulUpdatableCoe

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