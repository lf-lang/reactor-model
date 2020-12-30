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

-- A mapping from *exactly* a given set of input-dependency ids to (possibly empty) values.
def reaction.input {n : ℕ} (d : finset (fin n)) := {i // i ∈ d} → option value

-- A mapping from *exactly* a given set of output-dependency ids to (possibly empty) values.
-- This represents the ports of a reactor.
def reaction.output {n : ℕ} (d : finset (fin n)) := {i // i ∈ d} → option value

-- A mapping from port ids to (possibly empty) values.
-- This represents the ports of a reactor.
def reactor.ports (n : ℕ) := fin n → option value

-- A mapping from variable ids to (possibly empty) values.
-- This represents the state fields of a reactor.
def reactor.vars (n : ℕ) := fin n → option value

-- A port assignment where all values are empty.
@[reducible]
def reactor.ports.empty {n : ℕ} : reactor.ports n := λ _, none

-- A port assignment is "total" if all of its values are non-empty.
def reactor.ports.is_total {n : ℕ} (p : reactor.ports n) : Prop := 
  ∀ i, p i ≠ none

namespace temporary

  def map_to_map {α : Type*} {n n' : ℕ} (f : fin n → α) (h : n' = n) : fin n' → α := 
    λ i, f ⟨i.val, h ▸ i.property⟩

  notation f↑h := map_to_map f h

  def ports_to_input {n : ℕ} {dᵢ : finset (fin n)} (p : reactor.ports n) : reaction.input dᵢ :=
    λ i : {d // d ∈ dᵢ}, p i

  notation ↑p := ports_to_input p

  def output_to_ports {n : ℕ} {dₒ : finset (fin n)} (o : reaction.output dₒ) : reactor.ports n :=
    λ i : fin n, if h : i ∈ dₒ then o ⟨i, h⟩ else none

  notation ↑o := output_to_ports o

end temporary

namespace rel

  -- The proposition, that a given relation has the "function" property.
  def is_function {α β : Type*} (r : rel α β) : Prop :=
    ∀ a : α, ∃! b : β, r a b

  -- Produces the function corresponding to a given relation that has the function-property.
  noncomputable def function {α β : Type*} (r : rel α β) (h : r.is_function) : α → β :=
    λ a : α, (h a).some 

  end rel