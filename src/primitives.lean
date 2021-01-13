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

  open reactor

  -- A port assignment where all values are empty.
  @[reducible]
  def ports.empty (n : ℕ) : ports := list.repeat none n

  theorem empty_ports_cons (n : ℕ) :
    ports.empty (n + 1) = none :: ports.empty n :=
    by refl

  -- The proposition, that a given port assignment is empty.
  def is_empty (p : reactor.ports) : Prop :=
    p = ports.empty p.length

  -- A port assignment is "total" if all of its values are non-empty.
  def is_total (p : ports) : Prop := 
    p.all (λ e, e ≠ none)

  -- Merges a given port map onto another port map.
  -- The `last` ports override the `first` ports.
  def merge (first last : ports) : ports :=
    last.zip_with (<|>) first

  theorem merge_length (p p' : ports) : 
    (p.merge p').length = min p.length p'.length :=
    begin
      unfold merge,
      rw list.length_zip_with,
      apply min_comm
    end

  theorem merge_empty_is_neutral (p : ports) :
    p.merge (ports.empty p.length) = p := 
    begin
      unfold merge,
      induction p,
        refl,
        {
          rw [list.length_cons, empty_ports_cons, list.zip_with_cons_cons, p_ih],
          simp [(<|>)]
        }
    end

  theorem merge_skips_empty (first last : ports) (i : ℕ) :
    last.nth i = some none → (first.merge last).nth i = first.nth i := 
    begin
      assume h,
      unfold merge,
      rw list.nth_zip_with,
      rw h,
      rw option.map_some,
      unfold has_orelse.orelse,
      simp [(<*>)], 
      cases first.nth i
        ; simp
    end

end reactor.ports
