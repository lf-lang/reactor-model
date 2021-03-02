import data.nat.basic
import data.list.indexes
import data.list.nodup
import data.list.range

lemma list.find_indexes_nth_nmem {α : Type*} {l : list α} {n : ℕ} {p : α → Prop} [decidable_pred p] :
  ∀ {x}, l.nth n = some x → ¬(p x) → n ∉ (l.find_indexes p) :=
  sorry

lemma list.find_indexes_nth_none {α : Type*} {l : list α} {n : ℕ} {p : α → Prop} [decidable_pred p] :
  l.nth n = none → n ∉ (l.find_indexes p) :=
  sorry

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/ne.20of.20mem.20and.20not.20mem/near/228463288
lemma list.mem_nmem_ne {α : Type*} {l : list α} {x x' : α} (h : x ∈ l) (h' : x' ∉ l) : 
  x ≠ x' :=
  begin 
    rintro rfl,
    exact h' h
  end

lemma list.index_of_cons_lt {α : Type*} [decidable_eq α] {hd : α} {tl : list α} {x x' : α} (h : (hd :: tl).index_of x < (hd :: tl).index_of x') (hₘ : x ∈ tl) (hₘ' : x' ∈ tl) (hₙ : (hd :: tl).nodup) :
  tl.index_of x < tl.index_of x' :=
  begin
    have hₕ, from list.not_mem_of_nodup_cons hₙ,
    have hₓ, from list.mem_nmem_ne hₘ hₕ,
    have hₓ', from list.mem_nmem_ne hₘ' hₕ,
    have hₛ, from list.index_of_cons_ne tl hₓ,
    have hₛ', from list.index_of_cons_ne tl hₓ',
    rw [hₛ, hₛ'] at h,
    exact nat.succ_lt_succ_iff.mp h
  end

lemma list.index_of_erase_lt {α : Type*} [decidable_eq α] {l : list α} {e x x' : α} (h : l.index_of x < l.index_of x') (hₘ : x ∈ l.erase e) (hₘ' : x' ∈ l.erase e) (hₙ : l.nodup) :
  (l.erase e).index_of x < (l.erase e).index_of x' :=
  begin
    have hₕ : e ∉ l.erase e, from list.mem_erase_of_nodup hₙ,
    have hₓ, from list.mem_nmem_ne hₘ hₕ,
    have hₓ', from list.mem_nmem_ne hₘ' hₕ,
    cases l,
      case list.nil { 
        exfalso,
        exact hₘ
      },
      case list.cons {
        by_cases hc : l_hd = e,
          {
            rw [hc, list.erase_cons_head e l_tl] at hₘ hₘ' ⊢,
            exact list.index_of_cons_lt h hₘ hₘ' hₙ
          },
          {
            rw list.erase_cons_tail l_tl hc at hₘ hₘ' ⊢,
            have hₑ : x ≠ x', from sorry,
            by_cases hcₓ : x = l_hd,
              {
                rw [hcₓ, list.index_of_cons_self, list.index_of_cons],
                have hₑ', from ne.symm (ne_of_eq_of_ne (symm hcₓ) hₑ),
                simp [if_neg hₑ']
              },
              {
                rw list.index_of_cons_ne (l_tl.erase e) hcₓ,
                sorry
              }
          }
      }
  end

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Enth.20is.20either.20none/near/226562824
lemma option.join_eq_none {α : Type*} (o : option (option α)) : o.join = none ↔ o = none ∨ o = some none :=
  by rcases o with _|_|_; simp

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Eupdate_nth_comm/near/223010209
@[simp]
lemma list.update_nth_nil {α : Type*} (n : ℕ) (a : α) : [].update_nth n a = [] := rfl
lemma list.update_nth_comm {α : Type*} (a b : α) : ∀ {n m : ℕ} (h : n ≠ m) (l : list α),
  (l.update_nth n a).update_nth m b = (l.update_nth m b).update_nth n a
  | _ _ _ [] := by simp
  | 0 0 h (x :: t) := absurd rfl h
  | (n + 1) 0 h (x :: t) := by simp [list.update_nth]
  | 0 (m + 1) h (x :: t) := by simp [list.update_nth]
  | (n + 1) (m + 1) h (x :: t) := by { simp [list.update_nth], exact list.update_nth_comm (λ h', h $ nat.succ_inj'.mpr h') t}

-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Nodup.20Indices/near/224749989

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
