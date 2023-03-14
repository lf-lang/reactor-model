import ReactorModel.Objects.Reactor.ReactorType.Basic

open Reactor (Component)

namespace ReactorType

variable [ReactorType α] [ReactorType β]

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
  | notMem : (IsEmpty $ Member cmp i rtr)       → LawfulUpdate cmp i f rtr rtr

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

-- Note: We `ReactorType α` make a field instead of using `extends ReactorType α`, to avoid a 
--       diamond with `ReactorType.Indexable` later. 
class Updatable (α) where
  [inst : ReactorType α] 
  update : α → (cmp : Component.Valued) → ID → (cmp.type → cmp.type) → α  
  lawfulUpdate : ∀ rtr cmp i f, LawfulUpdate cmp i f rtr (update rtr cmp i f)




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
-- TODO: Keep this definition, but try to find a simpler way to construct an instance of this type
--       which can be used for `Reactor.Core`.
--       Actually, perhaps the solution is to use the recursive definition and have these fields be
--       theorems. Then you could lower the requirement of `[Indexable α]` to `[ReactorType α]` and
--       create an instance for `Reactor.Core`.
structure LawfulUpdate [Indexable α] 
    (rtr₁ rtr₂ : α) (cmp : Component.Valued) (i : ID) (f : cmp.type → cmp.type) : Prop where
  equiv     : rtr₁ ≈ rtr₂  
  unchanged : (c ≠ cmp ∨ j ≠ i) → rtr₁[c][j] = rtr₂[c][j]
  changed   : f <$> rtr₁[cmp][i] = rtr₂[cmp][i]

theorem LawfulUpdate.lift [Indexable α] [Indexable β] [LawfulCoe α β] {cmp f} {rtr₁ rtr₂ : α}
    (u : LawfulUpdate (rtr₁ : β) (rtr₂ : β) cmp i f) : LawfulUpdate rtr₁ rtr₂ cmp i f :=
  sorry

namespace LawfulUpdate

variable [Indexable α] {rtr₁ rtr₂ : α}

-- TODO: Rename and clean up these theorems.

theorem obj?_some_iff {cmp : Component.Valued} {f cmp' j} (u : LawfulUpdate rtr₁ rtr₂ cmp i f) :
    (∃ o₁, rtr₁[cmp'][j] = some o₁) ↔ (∃ o₂, rtr₂[cmp'][j] = some o₂) := 
  Equivalent.obj?_some_iff u.equiv

theorem ne_cmp_obj?_eq {cmp' : Component} {cmp : Component.Valued} {f} 
    (u : LawfulUpdate rtr₁ rtr₂ cmp i f) (hc : cmp' ≠ cmp := by simp) 
    (hr : cmp' ≠ .rtr := by simp) : rtr₁[cmp'] = rtr₂[cmp'] := by
  cases cmp'
  case rtr => contradiction
  case rcn => exact u.equiv.rcns
  all_goals funext j; exact u.unchanged $ .inl (by simp_all)

/-
theorem update_rtr_some_obj?_eq_cmp? {cmp' : Component} {cmp : Component.Valued}  {f j i' o}
    (h : rtr[.rtr][j] = some con) (hu : (rtr.update cmp i f)[.rtr][j] = some con') 
    (hc : cmp? cmp' con' i' = some o) (hn₁ : cmp' ≠ cmp := by simp) (hn₂ : cmp' ≠ .rtr := by simp) :
    cmp? cmp' con i' = some o :=
  sorry
-/

end LawfulUpdate
-/
end ReactorType