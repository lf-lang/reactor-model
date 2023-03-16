import ReactorModel.Objects.Reactor.ReactorType.Basic

open Reactor (Component)

namespace ReactorType

variable [ReactorType α] [ReactorType β] in section

def RootEqualUpTo (cmp : Component) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cmp ∨ j ≠ i) → cmp? c rtr₁ j = cmp? c rtr₂ j

-- Note: Without ID-uniqueness this can be satisfied by updating exactly one of the occurrences of
--       the target.
inductive LawfulMemUpdate (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) : α → α → Prop
  | final : 
    (RootEqualUpTo cmp i rtr₁ rtr₂) → (cmp? cmp rtr₁ i = some o) → (cmp? cmp rtr₂ i = f o) → 
    LawfulMemUpdate cmp i f rtr₁ rtr₂
  | nest : 
    (RootEqualUpTo .rtr j rtr₁ rtr₂) → (cmp? .rtr rtr₁ j = some n₁) → (cmp? .rtr rtr₂ j = some n₂) → 
    (LawfulMemUpdate cmp i f n₁ n₂) → LawfulMemUpdate cmp i f rtr₁ rtr₂

inductive LawfulUpdate (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) : α → α → Prop
  | update : (LawfulMemUpdate cmp i f rtr₁ rtr₂) → LawfulUpdate cmp i f rtr₁ rtr₂
  | notMem : (IsEmpty $ Member cmp i rtr)        → LawfulUpdate cmp i f rtr rtr

def LawfulUpdate.lift [LawfulCoe α β] {rtr₁ rtr₂ : α} {cmp i f} 
    (u : LawfulUpdate cmp i f (rtr₁ : β) (rtr₂ : β)) : LawfulUpdate cmp i f rtr₁ rtr₂ :=
  sorry -- might need coe ∘ update = update ∘ coe  

-- TODO: Should these Member defs/theorems actually be about `Updatable`?
def Member.fromLawfulUpdate {rtr₁ rtr₂ : α} {cmp i f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) : 
    (Member c j rtr₂) → Member c j rtr₁
  | final h  => final sorry 
  | nest h l => sorry 

theorem Member.Equivalent.from_lawfulUpdate 
    {rtr₁ rtr₂ : α} {cmp i f} (u : LawfulUpdate cmp i f rtr₁ rtr₂) (m : Member c j rtr₂) : 
    Member.Equivalent m (Member.fromLawfulUpdate u m) := by
  induction m
  case final => constructor
  case nest e => sorry

end

class Updatable (α) extends Extensional α where
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

/-
intro c j
    constructor
    intro l₁ l₂
    open ReactorType in
    by_cases Nonempty (Member cmp i rtr.core)
    case neg =>
      suffices h : Member c j (rtr.core.update cmp i f) = Member c j rtr.core from
        (cast_inj h).mp $ rtr.uniqueIDs.allEq (cast h l₁) (cast h l₂)
      simp [Core.update, h]
    case pos =>
      generalize hl : h.some = l
      have h : Member c j (rtr.core.update _ i f) = Member c j (Core.update.go _ i f l) := by
        simp [hl, Core.update, h]
      apply (cast_inj h).mp
      set l₁' := cast h l₁
      set l₂' := cast h l₂
      cases l
      case final =>
        simp [Core.update.go] at l₁' l₂'
        sorry
      case nest =>
        sorry
-/

/-
structure LawfulUpdate [Indexable α] 
    (rtr₁ rtr₂ : α) (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) : Prop where
  equiv     : rtr₁ ≈ rtr₂  
  unchanged : (c ≠ cmp ∨ j ≠ i) → rtr₁[c][j] = rtr₂[c][j]
  changed   : f <$> rtr₁[cmp][i] = rtr₂[cmp][i]
-/

end ReactorType