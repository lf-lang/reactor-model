import data.finset
import order.lexicographic

-- The type of opaque values that can be passed between reactors and processed by reactions.
-- Their equality has to be decidable, but beyond that their values are of no interest. Hence they
-- are modeled as `empty`.
variables (υ : Type*) [decidable_eq υ]

-- Rationale for using *functions* in the following definitions:
-- An intuitive approach for the definition of `input`, `output`, `ports` and `state` might be to
-- use vectors of `option value`. In the end `ports` and `state` are basically just that, because
-- they map *from* `fin n`. The reason functions are used over vectors, is that the definition of
-- `input` and `output` can then be constrained to only map over a very speicific set of ids (what
-- will later be a reaction's dependencies). Using vectors in this case would require an auxiliary
-- map that associates each of the indices of an `in-/output` with the indices of the `ports` from
-- which they were derived.

-- A list of values.
-- This represents the state fields of a reactor.
-- Since we don't ever need to work with the state fields within Lean, their definition is fuzzy
-- for the sake of simplicity (we don't need to define a `nₛ` on reactors and reactions).
def reactor.state_vars := list υ

-- A mapping from port ids to (possibly empty) values.
-- This represents the ports of a reactor.
@[derive has_append]
def reactor.ports := list (option υ)

namespace reactor.ports

  open reactor

  def correspond_at {υ} [decidable_eq υ] (i : finset ℕ) (p p' : ports υ) : Prop :=
    ∀ x ∈ i, p.nth x = p'.nth x

  instance (i : finset ℕ) : is_equiv (ports υ) (correspond_at i) := 
    {
      symm :=  begin unfold correspond_at, finish end,
      trans := begin unfold correspond_at, finish end,
      refl :=  begin unfold correspond_at, finish end
    }

  -- A port assignment where all values are empty.
  @[reducible]
  def empty (n : ℕ) : ports υ := list.repeat none n

  lemma empty_cons (n : ℕ) :
    empty υ (n + 1) = none :: empty υ n :=
    by refl

  -- The proposition, that a given port assignment is empty.
  def is_empty (p : ports υ) : Prop :=
    p = empty υ p.length

  -- The indices in the given port map that have a corresponding (non-`none`) value.
  noncomputable def inhabited_indices {υ} [decidable_eq υ] (p : ports υ) : list ℕ :=
    p.find_indexes (λ e, e ≠ none)

  lemma inhabited_indices_nodup (p : ports υ) : 
    list.nodup (inhabited_indices p) :=
    sorry

  -- Merges a given port map onto another port map.
  -- The `last` ports override the `first` ports, but the length remains that of `first`.
  def merge {υ} [decidable_eq υ] (first last : ports υ) : ports υ :=
    (last.zip_with (<|>) first) ++ 
    if first.length ≤ last.length then [] else empty υ (first.length - last.length)

  lemma merge_length (p p' : ports υ) : 
    (p.merge p').length = p.length :=
    begin
      unfold merge,
      simp,
      by_cases h : p.length ≤ p'.length, 
        finish,
        {
          rw if_neg h, 
          unfold empty,
          rw list.length_repeat,
          simp at h,
          rw min_eq_left (le_of_lt h),
          rw [← nat.add_sub_assoc (le_of_lt h), nat.add_sub_cancel_left],
        }
    end

  lemma merge_empty_is_neutral (p : ports υ) :
    p.merge (empty υ p.length) = p := 
    begin
      unfold merge,
      have h : list.length p ≤ list.length (empty υ (list.length p)), {
        unfold empty,
        finish
      },
      rw if_pos h,
      induction p,
        case list.nil { refl },
        case list.cons {
          rw list.length_cons,
          rw empty_cons, 
          rw list.zip_with_cons_cons, 
          have h' : (empty υ p_tl.length).length = p_tl.length, by apply list.length_repeat,
          have h'', from p_ih (le_of_eq (symm h')),  
          simp [(<|>)],
          rw list.append_nil at h'',
          exact h''
        }
    end

  lemma merge_skips_empty (first last : ports υ) (i : ℕ) :
    last.nth i = some none → (first.merge last).nth i = first.nth i := 
    begin
      assume h,
      unfold merge,
      by_cases hₗ : list.length first ≤ list.length last,
        {
          rw [if_pos hₗ, list.append_nil, list.nth_zip_with, h, option.map_some],
          unfold has_orelse.orelse,
          simp [(<*>)], 
          cases first.nth i
            ; simp
        },
        {
          rw if_neg hₗ,
          have hₗ' : (list.zip_with has_orelse.orelse last first).length = first.length, 
          from sorry,
          by_cases hᵢ : i < first.length,
            {
              have hᵢ' : i < (list.zip_with has_orelse.orelse last first).length, by finish,
              rw list.nth_append hᵢ',
              rw list.nth_le_nth hᵢ',
              rw list.nth_le_zip_with,
              sorry
            },
            {
              sorry
            }
        }
    end

  def clear_excluding {υ} [decidable_eq υ] (p : ports υ) (e : finset ℕ) : ports υ :=
    p.enum.map (λ iv, if (iv.1 ∈ e) then iv.2 else none)

end reactor.ports
