import data.finset
import primitives

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
  (body : ports → state_vars → (ports × state_vars)) 

namespace reaction

  instance coe_to_fun : has_coe_to_fun reaction :=
    ⟨_, (λ r, r.body)⟩

  noncomputable instance dec_eq : decidable_eq reaction := 
    classical.dec_eq _

  -- The proposition, that a given reaction fires on a given port map. This is only defined when
  -- the dimensions of the given port map match the reaction's input dimensions (`r.nᵢ`).
  def fires_on (r : reaction) (p : ports) : Prop :=
    ∃ (t : {x // x ∈ r.dᵢ}) (_ : t ∈ r.triggers) (v : value), p.nth t = some v

  instance dec_fires_on (r : reaction) (p : ports) : decidable (r.fires_on p) := 
    finset.decidable_dexists_finset

    -- A reaction will never fire on empty ports.
  --
  -- The `refl _` is the proof that the port map's dimensions are equal to the reaction's input
  -- dimensions (cf. `reaction.fires_on`).
  protected theorem no_in_no_fire (r : reaction) : 
    ∀ n : ℕ, ¬ r.fires_on (ports.empty n) := 
    begin 
      intro n,
      unfold reaction.fires_on,
      simp,
      intros i hₘ hₜ v,
      unfold ports.empty,
      rw list.nth_eq_some,
      simp,
      intro hᵢ,
      change ¬ none = some v,
      simp
    end

end reaction