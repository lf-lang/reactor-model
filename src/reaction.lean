import data.finset
import data.rel
import primitives
import reactor.primitives

-- Mappings from *exactly* a given set of dependency-indices to (possibly absent) values.
def reaction.dep_map {n : ℕ} (d : finset (fin n)) := {i // i ∈ d} → option value

open reaction

-- Reactions consist of a set of input dependencies `dᵢ`, output dependencies `dₒ`, `triggers` and
-- a function `body` that transforms a given input map and reactor state to an output map and a new
-- reactor state.
-- Since *actions* are not defined in this simplified model of reactors, the set of `triggers` is
-- simply a subset of the input dependencies `dᵢ`. The proof `nonempty_triggers` assures that a
-- reaction has at *least* some trigger.
structure reaction :=
  {nᵢ nₒ nₛ : ℕ}
  (dᵢ : finset (fin nᵢ)) 
  (dₒ : finset (fin nₒ))
  (triggers : finset {i // i ∈ dᵢ})
  (nonempty_triggers : triggers.nonempty)
  (body : rel (dep_map dᵢ × reactor.state nₛ) (dep_map dₒ × reactor.state nₛ)) 

namespace reaction

  -- The proposition, that a given reaction fires on a given port map.
  def fires_on (r : reaction) (p : reactor.ports r.nᵢ) : Prop :=
    ∃ (t : { x // x ∈ r.dᵢ }) (h : t ∈ r.triggers), p t ≠ none

  instance dec_fires_on (r : reaction) (is : reactor.ports r.nᵢ) : decidable (r.fires_on is) := 
    finset.decidable_dexists_finset

  -- A reaction is deterministic, if given equal inputs, running the body produces equal outputs
  -- This is only true if the reaction's body is actually a function.
  protected theorem determinism (r : reaction) (h : r.body.is_function) (i₁ i₂ : dep_map r.dᵢ) (s₁ s₂ : reactor.state r.nₛ) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body.function h) (i₁, s₁) = (r.body.function h) (i₂, s₂) := 
    assume ⟨hᵢ, hₛ⟩, hᵢ ▸ hₛ ▸ refl _

  -- A reaction will never fire on empty ports.
  protected theorem no_in_no_fire (r : reaction) : 
    ¬ (r.fires_on reactor.ports.empty) :=
    begin 
      rw reaction.fires_on,
      simp,
    end

  -- If a given port-assignment has no empty values then a reaction will definitely fire on them.
  protected theorem total_ins_fires (r : reaction) (p : reactor.ports r.nᵢ) :
    p.is_total → r.fires_on p :=
    begin
      intros hᵢ,
      -- Get a `t ∈ r.triggers` (with membership-proof `hₘ`).
      obtain ⟨t, hₘ⟩ := r.nonempty_triggers,
      -- Show that `p` has a value for `t` by virtue of `hᵢ`.
      have hₚ : p t ≠ none, from hᵢ t, 
      exact ⟨t, hₘ, hₚ⟩,
    end 

end reaction