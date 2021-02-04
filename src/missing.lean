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

-- Courtesy of Yakov Pechersky: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Nodup.20Indices/near/224749989

open list

variables {α β γ δ ε : Type*}

@[simp]
lemma foldr_with_index_nil (f : ℕ → α → β → β) (b : β) : 
  foldr_with_index f b nil = b := 
  rfl

@[simp]
lemma foldr_with_index_singleton (f : ℕ → α → β → β) (b : β) (a : α) :
  foldr_with_index f b [a] = f 0 a b :=
  rfl

@[simp]
lemma function.uncurry_comp_prod_map_id_left (f : α → β → γ) (g : δ → α) :
  function.uncurry f ∘ prod.map g id = function.uncurry (f ∘ g) :=
  by { ext ⟨d, e⟩, simp }

lemma foldr_with_index_cons (f : ℕ → α → β → β) (b : β) (a : α) (l : list α) :
  foldr_with_index f b (a :: l) = f 0 a (foldr_with_index (f ∘ nat.succ) b l) :=
  by simp [foldr_with_index_eq_foldr_enum, enum_eq_zip_range, range_succ_eq_map, zip_map_left]

@[simp]
lemma find_indexes_nil (p : α → Prop) [decidable_pred p] : 
  find_indexes p nil = nil := 
  rfl

@[simp]
lemma find_indexes_cons_true (p : α → Prop) [decidable_pred p] (a : α) (l : list α) (h : p a) :
  find_indexes p (a :: l) = 0 :: (find_indexes p l).map nat.succ :=
  begin
    suffices : map (prod.fst ∘ prod.map nat.succ id) (filter ((p ∘ prod.snd) ∘ prod.map nat.succ id)
      ((range l.length).zip l)) = map (nat.succ ∘ prod.fst)
        (filter (p ∘ prod.snd) ((range l.length).zip l)),
      { simpa [find_indexes_eq_map_indexes_values, indexes_values_eq_filter_enum, enum_eq_zip_range,
              range_succ_eq_map, h, filter, zip_map_left, filter_of_map] },
    congr
  end

@[simp]
lemma find_indexes_cons_false (p : α → Prop) [decidable_pred p] (a : α) (l : list α) (h : ¬ p a) :
  find_indexes p (a :: l) = (find_indexes p l).map nat.succ :=
  begin
    suffices : map (prod.fst ∘ prod.map nat.succ id) (filter ((p ∘ prod.snd) ∘ prod.map nat.succ id)
      ((range l.length).zip l)) = map (nat.succ ∘ prod.fst)
        (filter (p ∘ prod.snd) ((range l.length).zip l)),
      { simpa [find_indexes_eq_map_indexes_values, indexes_values_eq_filter_enum, enum_eq_zip_range,
              range_succ_eq_map, h, filter, zip_map_left, filter_of_map] },
    congr
  end

@[simp]
lemma nodup_find_indexes (l : list α) (p : α → Prop) [decidable_pred p] :
  (l.find_indexes p).nodup :=
  begin
    induction l with hd tl hl,
    { simp },
    { by_cases h : p hd;
      simpa [h, nat.succ_ne_zero] using nodup_map nat.succ_injective hl }
  end
