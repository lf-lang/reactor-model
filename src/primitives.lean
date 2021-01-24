import data.finset

-- Typealias via `notation`:
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Type.20alias 

-- The type of opaque values that can be passed between reactors and processed by reactions.
-- Their equality has to be decidable, but beyond that their values are of no interest. Hence they
-- are modeled as `empty`.
notation `value` := empty

-- Rationale for using *functions* in the following definitions:
-- An intuitive approach for the definition of `input`, `output`, `ports` and `state` might be to
-- use vectors of `option value`. In the end `ports` and `state` are basically just that, because
-- they map *from* `fin n`. The reason functions are used over vectors, is that the definition of
-- `input` and `output` can then be constrained to only map over a very speicific set of ids (what
-- will later be a reaction's dependencies). Using vectors in this case would require an auxiliary
-- map that associates each of the indices of an `in-/output` with the indices of the `ports` from
-- which they were derived.

-- A list of values values.
-- This represents the state fields of a reactor.
-- Since we don't ever need to work with the state fields within Lean, their definition is fuzzy
-- for the sake of simplicity (we don't need to define a `nₛ` on reactors and reactions).
def reactor.state_vars := list value

-- A mapping from port ids to (possibly empty) values.
-- This represents the ports of a reactor.
@[derive has_append]
def reactor.ports := list (option value)

namespace reactor.ports

  open reactor

  def correspond_at (i : finset ℕ) (p p' : ports) : Prop :=
    ∀ x ∈ i, p.nth x = p'.nth x

  instance (i : finset ℕ) : is_equiv ports (correspond_at i) := 
    {
      symm :=  begin unfold correspond_at, finish end,
      trans := begin unfold correspond_at, finish end,
      refl :=  begin unfold correspond_at, finish end
    }

  -- A port assignment where all values are empty.
  @[reducible]
  def empty (n : ℕ) : ports := list.repeat none n

  lemma empty_cons (n : ℕ) :
    empty (n + 1) = none :: empty n :=
    by refl

  -- The proposition, that a given port assignment is empty.
  def is_empty (p : ports) : Prop :=
    p = empty p.length

  -- The indices in the given port map that have a corresponding (non-`none`) value.
  def inhabited_indices (p : ports) : list ℕ :=
    p.enum.filter_map (λ ⟨i, e⟩, e.elim none (λ _, i))

  -- Merges a given port map onto another port map.
  -- The `last` ports override the `first` ports, but the length remains that of `first`.
  def merge (first last : ports) : ports :=
    (last.zip_with (<|>) first) ++ 
    if first.length ≤ last.length then [] else empty (first.length - last.length)

  lemma merge_length (p p' : ports) : 
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

  lemma merge_empty_is_neutral (p : ports) :
    p.merge (empty p.length) = p := 
    begin
      unfold merge,
      have h : list.length p ≤ list.length (empty (list.length p)), {
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
          have h' : (empty p_tl.length).length = p_tl.length, by apply list.length_repeat,
          have h'', from p_ih (le_of_eq (symm h')),  
          simp [(<|>)],
          rw list.append_nil at h'',
          exact h''
        }
    end

  lemma merge_skips_empty (first last : ports) (i : ℕ) :
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

end reactor.ports
