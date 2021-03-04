import data.nat.basic
import data.list.indexes
import data.list.nodup
import data.list.range
import tactic

lemma list.update_nth_same {α : Type*} (l : list (option α)) (n : ℕ) : 
  l.update_nth n (l.nth n).join = l :=
  sorry

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Eupdate_same/near/228774282
lemma list.update_same {α : Type*} (l : list α) (n : ℕ) (a a' : α) :
  (l.update_nth n a).update_nth n a' = l.update_nth n a' :=
  begin
    induction l with hd tl hl generalizing n,
    { simp [list.update_nth] },
    { cases n,
      { simp [list.update_nth] },
      { simp [list.update_nth, hl] } }
  end
  
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/index_of_erase_lt/near/228527125

@[simp] 
lemma list.sublist_nil {α : Type*} {l : list α} : l <+ [] ↔ l = [] :=
  begin
    split,
      { 
        rintro ⟨⟩,
        refl 
      },
      { 
        rintro rfl,
        refl 
      }
  end

lemma list.mem_of_mem_sublist {α : Type*} {l l' : list α} {x : α} (h : x ∈ l) (hl : l <+ l') :
  x ∈ l' :=
  begin
    induction hl with _ tl hd hl IH tl tl' hd hl IH,
      simpa using h,
      exact list.mem_cons_of_mem _ (IH h),
      { 
        rw [list.mem_cons_iff] at h ⊢,
        rcases h with h | h,
          exact or.inl h,
          exact or.inr (IH h) 
      }
  end

lemma list.index_of_lt_of_sublist {α : Type*} [decidable_eq α] {l l' : list α} {x x' : α}
  (h : l.index_of x < l.index_of x') (hl : l' <+ l)
  (hₘ : x ∈ l') (hₘ' : x' ∈ l') (hₙ : l.nodup) :
  l'.index_of x < l'.index_of x' :=
  begin
    induction hl with _ tl hd hl IH tl tl' hd hl IH,
    { simpa using hₘ },
    { refine IH _ hₘ hₘ' _,
      { have hne : ∀ z ∈ hl_l₁, z ≠ hd,
          { rintro z hz rfl,
            have : z ∈ tl := list.mem_of_mem_sublist hz hl,
            simpa [this] using hₙ },
        rwa [list.index_of_cons_ne _ (hne _ hₘ), list.index_of_cons_ne _ (hne _ hₘ'),
            nat.succ_lt_succ_iff] at h },
      { rw list.nodup_cons at hₙ,
        exact hₙ.right } },
    { rw list.mem_cons_iff at hₘ hₘ',
      rw list.nodup_cons at hₙ,
      rcases hₘ with rfl|hₘ;
      rcases hₘ' with rfl|hₘ',
      { simpa using h },
      { have hx' : x' ∈ tl' := list.mem_of_mem_sublist hₘ' hl,
        replace hx' : x' ≠ x := ne_of_mem_of_not_mem hx' hₙ.left,
        simp [hx'] },
      { have hx : x ∈ tl' := list.mem_of_mem_sublist hₘ hl,
        replace hx : x ≠ x' := ne_of_mem_of_not_mem hx hₙ.left,
        simpa [hx] using h },
      { have hx : x ∈ tl' := list.mem_of_mem_sublist hₘ hl,
        replace hx : x ≠ hd := ne_of_mem_of_not_mem hx hₙ.left,
        have hx' : x' ∈ tl' := list.mem_of_mem_sublist hₘ' hl,
        replace hx' : x' ≠ hd := ne_of_mem_of_not_mem hx' hₙ.left,
        rw [list.index_of_cons_ne _ hx, list.index_of_cons_ne _ hx', nat.succ_lt_succ_iff] at h ⊢,
        exact IH h hₘ hₘ' hₙ.right } }
  end

lemma list.index_of_erase_lt {α : Type*} [decidable_eq α] {l : list α} {e x x' : α}
  (h : l.index_of x < l.index_of x') (hₘ : x ∈ l.erase e) (hₘ' : x' ∈ l.erase e) (hₙ : l.nodup) :
  (l.erase e).index_of x < (l.erase e).index_of x' :=
    list.index_of_lt_of_sublist h (l.erase_sublist e) hₘ hₘ' hₙ

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
