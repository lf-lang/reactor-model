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
