import data.nat.basic
import data.list.indexes
import data.list.nodup
import data.list.range

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Eupdate_nth_comm/near/223010209
@[simp]
lemma list.update_nth_nil (α : Type) (n : ℕ) (a : α) : [].update_nth n a = [] := rfl
lemma list.update_nth_comm (α : Type) (a b : α) : Π (n m : ℕ) (h : n ≠ m) (l : list α),
  (l.update_nth n a).update_nth m b =
  (l.update_nth m b).update_nth n a
  | _ _ _ [] := by simp
  | 0 0 h (x :: t) := absurd rfl h
  | (n + 1) 0 h (x :: t) := by simp [list.update_nth]
  | 0 (m + 1) h (x :: t) := by simp [list.update_nth]
  | (n + 1) (m + 1) h (x :: t) := by { simp [list.update_nth], exact list.update_nth_comm n m (λ h', h $ nat.succ_inj'.mpr h') t}

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Nodup.20Indices/near/224669319
lemma nodup_zip_of_left {α β : Type*} {l : list α} (h : l.nodup) (l' : list β) :
  (l.zip l').nodup :=
  begin
    induction l with hd tl hl generalizing l',
    { simp },
    { cases l' with hd' tl',
      { simp },
      { rw [list.nodup_cons] at h,
        rw [list.zip_cons_cons, list.nodup_cons],
        exact ⟨λ H, h.left (list.mem_zip H).left, hl h.right _⟩ } }
  end

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Nodup.20Indices/near/224669319
lemma nodup_zip_of_right {α β : Type*} (l : list α) {l' : list β} (h : l.nodup) :
  (l.zip l').nodup :=
  begin
    induction l' with hd tl hl generalizing l,
    { simp },
    { cases l with hd' tl',
      { simp },
      { rw [list.nodup_cons] at h,
        rw [list.zip_cons_cons, list.nodup_cons],
        exact ⟨λ H, h.left (list.mem_zip H).left, hl _ h.right⟩ } }
  end

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Nodup.20Indices/near/224669319
@[simp] lemma nodup_enum {α : Type*} {l : list α} : l.enum.nodup :=
by { rw list.enum_eq_zip_range, exact nodup_zip_of_left (list.nodup_range _) _ }

lemma list.find_indexes_nodup {α : Type*} (p : α → Prop) [decidable_pred p] (l : list α) : 
  (l.find_indexes p).nodup :=
  begin
    rw list.find_indexes_eq_map_indexes_values,
    -- This sorry can't be fixed, because it doesn't *generally* hold that `prod.fst` is injective.
    -- It only holds here, i.e. where we know that all first elements are nodup.
    suffices h : (list.indexes_values p l).nodup, from list.nodup_map sorry h, 
    rw list.indexes_values_eq_filter_enum,
    suffices h : l.enum.nodup, from list.nodup_filter _ h,
    apply nodup_enum
  end