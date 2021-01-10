import data.finset
import nondet
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
  {nᵢ nₒ : ℕ}
  (dᵢ : finset (fin nᵢ)) 
  (dₒ : finset (fin nₒ))
  (triggers : finset {i // i ∈ dᵢ})
  (body : (ports nᵢ × state_vars) ~> (ports nₒ × state_vars)) 

namespace reaction

  -- The characteristic dimensions of a given reaction.
  def dims (r : reaction) : ℕ × ℕ :=
    (r.nᵢ, r.nₒ)

  -- The subtype of reactors with given fixed dimensions.
  protected def fixed (nᵢ nₒ: ℕ) : Type* := 
    { r : reaction // r.dims = (nᵢ, nₒ) }

  -- The proposition, that a given reaction fires on a given port map. This is only defined when
  -- the dimensions of the given port map match the reaction's input dimensions (hence `h`).
  def fires_on {n : ℕ} (r : reaction) (p : ports n) (h : r.nᵢ = n) : Prop :=
    ∃ (t : {x // x ∈ r.dᵢ}) (_ : t ∈ r.triggers), p (fin.cast h t) ≠ none

  instance dec_fires_on {n : ℕ} (r : reaction) (p : ports n) (h : r.nᵢ = n) : decidable (r.fires_on p h) := 
    finset.decidable_dexists_finset

  -- The proposition, that a given reaction is deterministic.
  def is_det (r : reaction) : Prop :=
    r.body.is_det

  -- If a reaction is deterministic, then running it on equal inputs produces equal outputs.
  protected theorem determinism (r : reaction) (h : r.is_det) (i₁ i₂ : ports r.nᵢ) (s₁ s₂ : state_vars) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body.det h) (i₁, s₁) = (r.body.det h) (i₂, s₂) := 
    assume ⟨hᵢ, hₛ⟩, hᵢ ▸ hₛ ▸ refl _

  -- A reaction will never fire on empty ports.
  --
  -- The `refl _` is the proof that the port map's dimensions are equal to the reaction's input
  -- dimensions (cf. `reaction.fires_on`).
  protected theorem no_in_no_fire (r : reaction) : 
    ¬ r.fires_on ports.empty (refl _) :=
    begin 
      rw reaction.fires_on,
      simp
    end

  -- If a given port map has no empty values (i.e. is total) then a reaction will definitely fire
  -- on it.
  --
  -- Two technicalities are that the reaction's triggers are non-empty, and the port map has the
  -- right dimensions.
  protected theorem total_ins_fires {n : ℕ} (r : reaction) (p : ports n) (hₜ : r.triggers.nonempty) (hₙ : r.nᵢ = n) :
    p.is_total → r.fires_on p hₙ :=
    begin
      intros hᵢ,
      -- Get a `t ∈ r.triggers` (with membership-proof `hₘ`).
      obtain ⟨t, hₘ⟩ := hₜ,
      -- Show that `p` has a value for `t` (cast to `fin n`) by virtue of `hᵢ`.
      have hₚ : p (fin.cast hₙ t) ≠ none, from hᵢ (fin.cast hₙ t), 
      exact ⟨t, hₘ, hₚ⟩
    end 

end reaction