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
  (dᵢ : finset ℕ) 
  (dₒ : finset ℕ)
  (triggers : finset {i // i ∈ dᵢ})
  (body : (ports × state_vars) ~> (ports × state_vars)) 

noncomputable instance : decidable_eq reaction := classical.dec_eq _

namespace reaction

  -- The proposition, that a given reaction fires on a given port map. This is only defined when
  -- the dimensions of the given port map match the reaction's input dimensions (`r.nᵢ`).
  def fires_on (r : reaction) (p : ports) : Prop :=
    ∃ (t : {x // x ∈ r.dᵢ}) (_ : t ∈ r.triggers), p.nth t ≠ none

  instance dec_fires_on (r : reaction) (p : ports) : decidable (r.fires_on p) := 
    finset.decidable_dexists_finset

  -- The proposition, that a given reaction is deterministic.
  def is_det (r : reaction) : Prop :=
    r.body.is_det

  -- If a reaction is deterministic, then running it on equal inputs produces equal outputs.
  protected theorem determinism (r : reaction) (h : r.is_det) (i₁ i₂ : ports) (s₁ s₂ : state_vars) :
    i₁ = i₂ ∧ s₁ = s₂ → (r.body.det h) (i₁, s₁) = (r.body.det h) (i₂, s₂) := 
    assume ⟨hᵢ, hₛ⟩, hᵢ ▸ hₛ ▸ refl _

  -- A reaction will never fire on empty ports.
  --
  -- The `refl _` is the proof that the port map's dimensions are equal to the reaction's input
  -- dimensions (cf. `reaction.fires_on`).
  protected theorem no_in_no_fire (r : reaction) : 
    ∀ n : ℕ, ¬ r.fires_on (ports.empty n) :=
    begin 
      intro n,
      rw reaction.fires_on,
      simp,
      intros x hₘ,
      sorry
    end

  -- If a given port map has no empty values (i.e. is total) then a reaction will definitely fire
  -- on it.
  --
  -- Two technicalities are that the reaction's triggers are non-empty, and the port map has the
  -- right dimensions.
  protected theorem total_ins_fires {n : ℕ} (r : reaction) (p : ports) (hₜ : r.triggers.nonempty) :
    p.is_total → r.fires_on p :=
    begin
      intros hᵢ,
      -- Get a `t ∈ r.triggers` (with membership-proof `hₘ`).
      obtain ⟨t, hₘ⟩ := hₜ,
      -- Show that `p` has a value for `t` by virtue of `hᵢ`.
      have hₚ : p.nth t ≠ none, from sorry, -- from hᵢ t, 
      exact ⟨t, hₘ, hₚ⟩
    end 

end reaction