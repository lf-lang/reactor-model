import data.finset
import order.lexicographic
import mathlib

-- The type of opaque values that can be passed between reactors and processed by reactions.
-- Their equality has to be decidable, but beyond that their values are of no interest.
variables (υ : Type*) [decidable_eq υ]

-- A list of state variables as used by reactors.
-- The indices into the list can be viewed as the IDs for individual state variables.
def reactor.state_vars := list υ

-- A list of ports as used by reactors.
-- The indices into the list are used as the IDs for individual state variables.
-- Absent values are represented by `option.none`.
-- We often call an instance of this type a "port assignment".
@[derive has_append]
def reactor.ports := list (option υ)

namespace reactor
namespace ports

  variable {υ}

  -- Ports can be input- our output-ports.
  -- Making this distinction explicit is useful for avoiding code duplication for some algorithms.
  inductive role
    | input : role
    | output : role

  -- Returns the opposite of the given role.
  @[reducible]
  def role.opposite : role → role 
    | role.input := role.output
    | role.output := role.input

  -- Accessing in index that contains an absent value, and accessing an index 
  -- that isn't part of the list should both return `none`.
  -- This helps avoid nested optional values.
  def nth (p : ports υ) (n : ℕ) : option υ := (p.nth n).join

  -- Exentionality of ports.
  @[ext]
  lemma ext {p p' : ports υ} (hₚ : p.nth = p'.nth) (hₗ : p.length = p'.length) : p = p' :=
    begin
      ext1 x,
      by_cases hc : x < p.length,
        {
          have h' : ∀ n, p.nth n = p'.nth n, from congr_fun hₚ,
          unfold nth at h',
          replace h' := h' x,
          rw list.nth_le_nth hc at h' ⊢,
          have hj : ∀ n : option υ, (option.some n).join = n, by finish,
          rw hj at h',
          rw hₗ at hc,
          rw list.nth_le_nth hc at h' ⊢,
          rw hj at h',
          rw h'
        },
        {
          have h, from not_lt.mp hc,
          rw hₗ at hc,
          have h', from not_lt.mp hc,
          rw [list.nth_len_le h, list.nth_len_le h']
        }
    end

  -- The proposition that two port assignments have the same values at given indices.
  def eq_at (i : finset ℕ) (p p' : ports υ) : Prop := ∀ x ∈ i, p.nth x = p'.nth x

  notation p =i= q := (eq_at i p q)

  -- For fixed indices, `reactor.ports.eq_at` is reflexive.
  @[refl]
  lemma eq_at_refl (i : finset ℕ) (p : ports υ) : p =i= p := by tauto

  -- For fixed indices, `reactor.ports.eq_at` is symmetric.
  @[symm]
  lemma eq_at_symm {i : finset ℕ} {p p' : ports υ} (h : p =i= p') : p' =i= p := by tauto

  -- For fixed indices, `reactor.ports.eq_at` is transitive.
  @[trans]
  lemma eq_at_trans {i : finset ℕ} {p₁ p₂ p₃ : ports υ} (h₁₂ : p₁ =i= p₂) (h₂₃ : p₂ =i= p₃) : 
    p₁ =i= p₃ :=
    assume x hₓ, eq.trans (h₁₂ x hₓ) (h₂₃ x hₓ)

  variable υ

  -- A port assignment that only contains absent values.
  def empty (n : ℕ) : ports υ := list.repeat none n

  -- Empty ports can be constructed from absent values.
  @[simp]
  lemma empty_cons (n : ℕ) : empty υ (n + 1) = none :: empty υ n := by refl

  variable {υ}

  -- The proposition, that a given port assignment is empty.
  def is_empty (p : ports υ) : Prop := (p = empty υ p.length)

  -- The set of indices for which the given port assignments have different values.
  noncomputable def index_diff (before after : ports υ) : finset ℕ :=
    @finset.filter _ 
      (λ i, before.nth i ≠ after.nth i) 
      (classical.dec_pred _) 
      (finset.range (max before.length after.length))

  -- Index-diffing is commutative.
  lemma index_diff_comm (before after : ports υ) : before.index_diff after = after.index_diff before :=
    begin
      unfold index_diff,
      rw max_comm,
      congr,
      ext,
      tauto
    end

  -- The index-diff of equal port assignments is empty.
  @[simp]
  lemma index_diff_eq_ports_empty {p p' : ports υ} (h : p = p') : p.index_diff p' = ∅ :=
    by simp [index_diff, h]

  -- An index-diff is always a subset of the index-range of the longer port assignment.
  @[simp]
  lemma index_diff_range (before after : ports υ) :
    before.index_diff after ⊆ finset.range (max before.length after.length) :=
    begin
      unfold index_diff,
      simp only [(⊆)],
      intro x,
      rw finset.mem_filter,
      intro h,
      exact h.left
    end

  -- The indices in the given port assignment that have a non-absent value.
  def inhabited_indices (p : ports υ) : finset ℕ :=
    (finset.range p.length).filter (λ i, p.nth i ≠ none)

  -- Indicies with an absent value are not part of a port assignments inhabited indices.
  lemma inhabited_indices_none {p : ports υ} {o : ℕ} (h : p.nth o = none) : 
    o ∉ p.inhabited_indices :=
    by simp [inhabited_indices, not_congr finset.mem_filter, h]
    
  -- Merges a given port assignment *onto* another one.
  -- The `src` ports override the `dst` ports, but the length remains that of `dst`.
  def merge (dst src : ports υ) : ports υ :=
    (src.zip_with (<|>) dst) ++ (dst.drop src.length)

  -- The length of merged ports is that of the first instance.
  @[simp]
  lemma merge_length (dst src : ports υ) : (dst.merge src).length = dst.length :=
    begin
      unfold merge,
      by_cases h : dst.length ≤ src.length, 
        simp [h],
        {
          rw not_le at h,
          rw [list.length_append, list.length_zip_with, list.length_drop],
          rw [min_eq_left_of_lt h, ←nat.add_sub_assoc (le_of_lt h), nat.add_sub_cancel_left]
        }
    end

  -- If the source of a merge contains an absent value for some port, that port stays unaffected.
  -- The proof is a bit long, as there are many cases to be covered.
  @[simp]
  lemma merge_none_eq (dst : ports υ) {src : ports υ} {p : ℕ} (h : src.nth p = none) :
    (dst.merge src).nth p = dst.nth p :=
    begin
      replace h := option.join_eq_none.mp h,
      unfold merge,
      simp only [ports.nth, list.nth_zip_with],
      by_cases hcₗ : dst.length ≤ src.length,
        {
          simp only [list.drop_eq_nil_iff_le.mpr hcₗ, list.append_nil, list.nth_zip_with, option.map_eq_map, option.bind_eq_bind, (<*>)],
          cases h,
            all_goals { simp [h] },
            {
              rw list.nth_eq_none_iff at h,
              simp [list.nth_eq_none_iff.mpr (has_le.le.trans hcₗ h)]
            },
            {
              rw list.nth_eq_some at h,
              by_cases hc : list.nth dst p = none,
                simp [hc],
                { simp at hc, simp [list.nth_le_nth hc] }
            }
        },
        {
          rw not_le at hcₗ,
          by_cases hc : p < (list.zip_with has_orelse.orelse src dst).length,
            {
              simp only [list.nth_append hc, list.nth_zip_with, list.map_eq_map, option.bind_eq_bind, (<*>)],
              congr,
              rw [list.length_zip_with, min_eq_left_of_lt hcₗ] at hc,
              cases h,
                {
                  exfalso,
                  have, from not_lt_of_le (list.nth_eq_none_iff.mp h),
                  contradiction
                },
                simp [h, list.nth_le_nth (has_lt.lt.trans hc hcₗ)]
            },
            {
              replace hc := le_of_not_lt hc,
              rw list.nth_append_right hc,
              rw [list.length_zip_with, min_eq_left_of_lt hcₗ] at hc ⊢,
              rw list.nth_drop,
              rw ←nat.add_sub_assoc hc,
              simp
            }
        }
    end

  example {n m x : ℕ} (h : n - x < m - x) : n < m := begin
    exact nat.lt_of_sub_lt_sub_right h,
  end

  -- Any index beyond the source ports will remain unchanged by a merge.
  @[simp] 
  lemma merge_after_src_eq_dst (dst : ports υ) {src : ports υ} {p : ℕ} (h : src.length ≤ p) : 
    (dst.merge src).nth p = dst.nth p :=
    begin
      have hₙ, from list.nth_len_le h,
      have hj, from option.join_eq_none.mpr (or.inl hₙ),
      exact merge_none_eq _ hj
    end

  -- If we merge "too few" ports, then the diff above is always empty. 
  lemma merge_index_diff_range_sub_src {dst src : ports υ} (hₗ : src.length ≤ dst.length) : 
    dst.index_diff (dst.merge src) ⊆ finset.range src.length :=
    begin
      simp only [(⊆)],
      intros x hₓ,
      simp [index_diff] at hₓ,
      by_cases hc : x ≥ src.length,
        {
          exfalso,
          have, from merge_after_src_eq_dst dst hc,
          replace hₓ := ne.symm hₓ.right,
          contradiction,
        },
        exact finset.mem_range.mpr (not_le.mp hc)
    end 

  -- The indices that change from a merge have to be less than the length of the destination ports.
  lemma merge_index_diff_range_sub_dst (dst src : ports υ) :
    dst.index_diff (dst.merge src) ⊆ finset.range dst.length :=
    begin
      simp only [(⊆)],
      intros x hₓ,
      simp [merge, index_diff] at hₓ,
      replace hₓ := hₓ.left,
      cases hₓ,
        exact list.mem_range.mpr hₓ, 
        {
          by_cases h : list.length dst ≤ list.length src,
            {
              rw [min_comm, min_eq_left h, nat.sub_eq_zero_of_le h] at hₓ,
              exact list.mem_range.mpr hₓ
            },
            {
              rw not_le at h,
              rw [min_eq_left_of_lt h, ←nat.add_sub_assoc (le_of_lt h), nat.add_sub_cancel_left] at hₓ,
              exact list.mem_range.mpr hₓ
            }
        }
    end

  -- The indices that change from a merge have to be less than the length of the source ports.
  lemma merge_index_diff_range_sub_src' (dst src : ports υ) : 
    dst.index_diff (dst.merge src) ⊆ finset.range src.length :=
    begin
      by_cases h : src.length ≤ dst.length,
        exact merge_index_diff_range_sub_src h,
        {
          have h', from index_diff_range dst (dst.merge src),
          simp only [(⊆)] at h' ⊢,
          intro x,
          simp only [finset.mem_range] at h' ⊢,
          intro hᵢ,
          have h'', from h' hᵢ,
          norm_num at h'',
          rw not_le at h,
          transitivity,
            exact h'',
            exact h
        }
    end

  -- The index-diff of merging `src` onto `dst` is a subset of the inhabited indices of `src`.
  lemma merge_index_diff_sub_inhabited (dst src : ports υ) : 
    dst.index_diff (dst.merge src) ⊆ src.inhabited_indices :=
    begin
      simp only [(⊆)],
      by_contradiction,
      rw not_forall at h,
      obtain ⟨x, hₓ⟩ := h,
      rw not_imp at hₓ,
      obtain ⟨hd, hᵢ⟩ := hₓ,
      unfold inhabited_indices at hᵢ,
      rw not_congr finset.mem_filter at hᵢ,
      cases not_and_distrib.mp hᵢ,
        {
          have h', from merge_index_diff_range_sub_src' dst src,
          simp only [(⊆)] at h',
          have hc, from h' hd,
          contradiction
        },
        {
          have h' : src.nth x = none, by finish,
          have hₑ, from merge_none_eq dst h',
          unfold index_diff at hd,
          rw [finset.mem_filter, hₑ] at hd,
          replace hd := hd.right,
          contradiction,
        }
    end

end ports
end reactor

