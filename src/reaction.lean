import data.finset
import data.rel
import primitives

open reaction
open reactor

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
  (body : rel (input dᵢ × vars nₛ) (output dₒ × vars nₛ)) 

namespace reaction

  -- The characteristic dimensions of a given reaction.
  def dimensions (r : reaction) : ℕ × ℕ × ℕ :=
    (r.nᵢ, r.nₒ, r.nₛ)

  -- The subtype of reactors with given fixed dimensions.
  protected def fixed (nᵢ nₒ nₛ : ℕ) : Type* := 
    { r : reaction // r.dimensions = (nᵢ, nₒ, nₛ) }

  -- The proposition, that a given reaction fires on a given port map.
  def fires_on (r : reaction) (p : ports r.nᵢ) : Prop :=
    ∃ (t : { x // x ∈ r.dᵢ }) (h : t ∈ r.triggers), p t ≠ none

  instance dec_fires_on (r : reaction) (is : ports r.nᵢ) : decidable (r.fires_on is) := 
    finset.decidable_dexists_finset

  -- A reaction is deterministic, if given equal inputs, running the body produces equal outputs
  -- This is only true if the reaction's body is actually a function.
  protected theorem determinism (r : reaction) (h : r.body.is_function) (i₁ i₂ : input r.dᵢ) (v₁ v₂ : vars r.nₛ) :
    i₁ = i₂ ∧ v₁ = v₂ → (r.body.function h) (i₁, v₁) = (r.body.function h) (i₂, v₂) := 
    assume ⟨hᵢ, hₛ⟩, hᵢ ▸ hₛ ▸ refl _

  -- A reaction will never fire on empty ports.
  protected theorem no_in_no_fire (r : reaction) : 
    ¬ (r.fires_on ports.empty) :=
    begin 
      rw reaction.fires_on,
      simp
    end

  -- If a given port-assignment has no empty values then a reaction will definitely fire on them.
  protected theorem total_ins_fires (r : reaction) (p : ports r.nᵢ) :
    p.is_total → r.fires_on p :=
    begin
      intros hᵢ,
      -- Get a `t ∈ r.triggers` (with membership-proof `hₘ`).
      obtain ⟨t, hₘ⟩ := r.nonempty_triggers,
      -- Show that `p` has a value for `t` by virtue of `hᵢ`.
      have hₚ : p t ≠ none, from hᵢ t, 
      exact ⟨t, hₘ, hₚ⟩
    end 

end reaction