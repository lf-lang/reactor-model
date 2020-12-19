import data.finset
import primitives
import reactor.primitives

-- Mappings from *exactly* a given set of {in,out}put dependency-indices to (possibly absent)
-- values.
--? It should be possible to extract the "core" of these definitions into a single definition and
--? then just have `input` and `output` be typealiases for that core.
namespace reaction 

  def input  {nᵢ : ℕ} (dᵢ : finset (fin nᵢ)) := {i // i ∈ dᵢ} → (option value)
  def output {nₒ : ℕ} (dₒ : finset (fin nₒ)) := {o // o ∈ dₒ} → (option value)

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
structure reaction (nᵢ nₒ nₛ : ℕ) :=
  (dᵢ : finset (fin nᵢ)) 
  (dₒ : finset (fin nₒ))
  (triggers : finset {i // i ∈ dᵢ})
  (body : input dᵢ → reactor.state nₛ → (output dₒ × reactor.state nₛ)) 

namespace reaction

  -- (1) Get R's triggers T.
  -- (2) Coerce the elements in T to be the input type of P.
  -- (3) Get the image I of (T through P).
  -- (4) Erase the absent value (`none`) from I.
  -- (4) If I is empty (contained nothing but the absent value), R is not triggered by P.
  def is_triggered_by {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) (is : reactor.ports nᵢ) : Prop :=
    let ts : finset (fin nᵢ) := r.triggers.map ⟨λ i, ↑i, subtype.coe_injective⟩ in
    let i : finset (option value) := ts.image is in
    let vs := i.erase none in
    vs.nonempty

  -- A reaction is deterministic, if given equal inputs and states, running the body produces equal
  -- outputs and states. 
  -- Since a reaction's body is a function, determinism is trivially fulfilled.
  protected theorem determinism {nᵢ nₒ nₛ : ℕ} (r : reaction nᵢ nₒ nₛ) (i₁ i₂ : input r.dᵢ) (s₁ s₂ : reactor.state nₛ) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body i₁ s₁) = (r.body i₂ s₂) := 
    assume h, congr (congr_arg r.body h.left) h.right

end reaction