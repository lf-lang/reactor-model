import data.rel
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

-- A priority for a reaction, where 0 is the highest priority.
@[reducible, derive fintype, derive has_lt, derive linear_order]
def reaction.priority (n : ℕ) := fin n

instance {n : ℕ} : is_total (reaction.priority n) has_lt.lt := sorry

-- A list of values values.
-- This represents the state fields of a reactor.
-- Since we don't ever need to work with the state fields within Lean, their definition is fuzzy
-- for the sake of simplicity (we don't need to define a `nₛ` on reactors and reactions).
def reactor.state_vars := list value

-- A mapping from port ids to (possibly empty) values.
-- This represents the ports of a reactor.
def reactor.ports (n : ℕ) := fin n → option value

namespace reactor.ports

  -- A port assignment where all values are empty.
  @[reducible]
  def empty (n : ℕ) : reactor.ports n := λ _, none

  -- A port assignment is "total" if all of its values are non-empty.
  def is_total {n : ℕ} (p : reactor.ports n) : Prop := 
    ∀ i, p i ≠ none

  -- Merges a given port map onto another port map.
  -- The `last` ports override the `first` ports.
  def merge {n : ℕ} (first last : reactor.ports n) : reactor.ports n :=
    λ i : fin n, (last i).elim (first i) (λ v, some v)

end reactor.ports

namespace rel

  -- The proposition, that a given relation has the "function" property.
  def is_function {α β : Type*} (r : rel α β) /-(f : α → β)-/ : Prop :=
    ∀ a : α, ∃! b : β, r a b
    -- ∀ (a : α) (b : β), r a b ↔ (f a = b)

  -- Produces the function corresponding to a given relation that has the function-property.
  noncomputable def function {α β : Type*} (r : rel α β) (h : r.is_function) : α → β :=
    λ a : α, (h a).some 

end rel

--! New/Old notation: abbreviation C := ℕ 

