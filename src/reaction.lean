import data.finset
import primitives
import reactor.primitives

open classical

-- Mappings from *exactly* a given set of {in,out}put dependency-indices to (possibly absent)
-- values.
--? It should be possible to extract the "core" of these definitions into a single definition and
--? then just have `input` and `output` be typealiases for that core.
namespace reaction 

  protected def input {nᵢ : ℕ} (dᵢ : finset (fin nᵢ)) := {i // i ∈ dᵢ} → (option value)  
  protected def output {nₒ : ℕ} (dₒ : finset (fin nₒ)) := {o // o ∈ dₒ} → (option value)

end reaction
open reaction

-- Reactions consist of a set of input dependencies `dᵢ`, output dependencies `dₒ`, `triggers` and
-- a function `body` that transforms a given input map and state to an output map and a new state.
-- Since *actions* are not defined in this simplified model of reactors, the set of `triggers` is
-- simply a subset of the input dependencies `dᵢ`.
--
--? Define the body as a relation, define what determinism means for reactions (namely that the
--? relation is actually a function), and then prove that determinism holds for more complex
--? objects if the reactions themselves are deterministic.
--? That way it would be more clear what is actually being shown: reactors are deterministic, if
--? the underlying reaction body (the foreign code) behaves like a function.
--
--? Define a coercion from reactions with smaller bounds to ones with higher bounds, if necessary.
structure reaction :=
  {nᵢ nₒ nₛ : ℕ}
  (dᵢ : finset (fin nᵢ)) 
  (dₒ : finset (fin nₒ))
  (triggers : finset {i // i ∈ dᵢ})
  (body : reaction.input dᵢ → reactor.state nₛ → (reaction.output dₒ × reactor.state nₛ)) 

namespace reaction

  def is_triggered_by (r : reaction) (is : reactor.ports r.nᵢ) :=
    ∃ (t : { x // x ∈ r.dᵢ }) (h : t ∈ r.triggers), is t ≠ none

  instance decidable_is_triggered_by (r : reaction) (is : reactor.ports r.nᵢ) : 
    decidable (r.is_triggered_by is) := finset.decidable_dexists_finset

  -- A reaction is deterministic, if given equal inputs and states, running the body produces equal
  -- outputs and states. 
  -- Since a reaction's body is a function, determinism is trivially fulfilled.
  protected theorem determinism (r : reaction) (i₁ i₂ : reaction.input r.dᵢ) (s₁ s₂ : reactor.state r.nₛ) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body i₁ s₁) = (r.body i₂ s₂) := 
    assume ⟨hᵢ, hₛ⟩, hᵢ ▸ hₛ ▸ refl _

  -- A reaction will never trigger for absent ports.
  protected theorem no_in_no_trig (r : reaction) : 
    r.is_triggered_by reactor.ports.absent = false :=
    begin 
      rw reaction.is_triggered_by,
      simp,
    end

  -- If a given port-assignment has no absent values and a reaction contains at least some trigger,
  -- then that reaction will definitely trigger for the given ports.
  protected theorem all_ins_nempty_trigs (r : reaction) (p : reactor.ports r.nᵢ) :
    (∀ i : fin r.nᵢ, p i ≠ none) → r.triggers.nonempty → r.is_triggered_by p :=
    begin
      intros hᵢ hₜ,
      have t : { i // i ∈ r.dᵢ }, from hₜ.some,
      have tm : t ∈ r.triggers, from sorry,
      have ptn : p t ≠ none, from hᵢ t,
      exact ⟨t, tm, ptn⟩,
    end 

end reaction