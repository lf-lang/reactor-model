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

namespace reactor.ports
open reactor

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

  @[ext]
  lemma ext {p p' : ports υ} (h : p.nth = p'.nth) : p = p' :=
    begin
      sorry
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
  def is_empty (p : ports υ) : Prop := p = empty υ p.length

  -- The set of indices for which the given port assignments have different values.
  noncomputable def index_diff (before after : ports υ) : finset ℕ :=
    @finset.filter _ 
      (λ i, before.nth i ≠ after.nth i) 
      (classical.dec_pred _) 
      (finset.range (max before.length after.length))

  -- The index diff of equal port assignments is empty.
  @[simp]
  lemma index_diff_eq_ports_empty {p p' : ports υ} (h : p = p') : p.index_diff p' = ∅ :=
    by simp [index_diff, h]

  -- The indices in the given port assignment that have a non-absent value.
  def inhabited_indices (p : ports υ) : finset ℕ :=
    (p.find_indexes (λ e, e ≠ none)).to_finset

  -- Indicies with an absent value are not part of a port assignments inhabited indices.
  lemma inhabited_indices_none {p : ports υ} {o : ℕ} (h : p.nth o = none) :
    o ∉ p.inhabited_indices :=
    begin
      cases option.join_eq_none.mp h with hc hc',
        {
          unfold inhabited_indices,
          rw not_congr list.mem_to_finset,
          exact list.find_indexes_nth_none hc
        },
        simp [inhabited_indices, list.find_indexes_nth_nmem hc']
    end
    
  -- Merges a given port assignment *onto* another one.
  -- The `src` ports override the `dst` ports, but the length remains that of `dst`.
  def merge (dst src : ports υ) : ports υ :=
    (src.zip_with (<|>) dst) ++ 
    if dst.length ≤ src.length then [] else empty υ (dst.length - src.length)

  -- The length of merged ports is that of the first instance.
  @[simp]
  lemma merge_length (p p' : ports υ) : 
    (p.merge p').length = p.length :=
    begin
      simp [merge],
      by_cases h : p.length ≤ p'.length, 
        finish,
        {
          simp [if_neg h, empty, list.length_repeat] at h ⊢, 
          rw [min_eq_left (le_of_lt h), ←nat.add_sub_assoc (le_of_lt h), nat.add_sub_cancel_left]
        }
    end

  -- Merging empty ports does not change anything.
  lemma merge_empty_neutral (p : ports υ) :
    p.merge (empty υ p.length) = p := 
    begin
      unfold merge,
      have h : list.length p ≤ list.length (empty υ (list.length p)), by simp [empty],
      rw if_pos h,
      induction p,
        case list.nil { refl },
        case list.cons {
          rw [list.length_cons, empty_cons, list.zip_with_cons_cons], 
          have h' : (empty υ p_tl.length).length = p_tl.length, by apply list.length_repeat,
          have h'', from p_ih (le_of_eq (symm h')),  
          simp [(<|>)],
          rw list.append_nil at h'',
          exact congr_arg (list.cons p_hd) h'',
        }
    end

end reactor.ports
