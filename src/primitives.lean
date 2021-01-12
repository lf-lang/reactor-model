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
def reactor.ports := list (option value)

namespace reactor.ports

  -- A port assignment where all values are empty.
  @[reducible]
  def empty (n : ℕ) : reactor.ports := list.repeat none n

  -- The proposition, that a given port assignment is empty.
  def is_empty (p : reactor.ports) : Prop :=
    p = reactor.ports.empty p.length

  -- A port assignment is "total" if all of its values are non-empty.
  def is_total (p : reactor.ports) : Prop := 
    p.all (λ e, e ≠ none)

  -- Merges a given port map onto another port map.
  -- The `last` ports override the `first` ports.
  def merge (first last : reactor.ports) : reactor.ports :=
    last.zip_with (<|>) first

  theorem merge_empty_is_neutral (p : reactor.ports) :
    p.merge (reactor.ports.empty p.length) = p := 
    sorry

  theorem merge_skips_empty (first last : reactor.ports) (i : ℕ) :
    last.nth i = none → (first.merge last).nth i = first.nth i := 
    begin
      assume h,
      rw reactor.ports.merge,
      sorry
    end

end reactor.ports
