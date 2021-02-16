import data.finset
import primitives

open reactor

-- Reactions consist of a set of input dependencies `dᵢ`, output dependencies `dₒ`, `triggers` and
-- a function `body` that transforms a given input map and reactor state to an output map and a new
-- reactor state.
-- Since *actions* are not defined in this simplified model of reactors, the set of `triggers` is
-- simply a subset of the input dependencies `dᵢ`. The proof `nonempty_triggers` assures that a
-- reaction has at *least* some trigger.
structure reaction (υ : Type*) [decidable_eq υ] :=
  (dᵢ : finset ℕ) 
  (dₒ : finset ℕ)
  (triggers : finset {i // i ∈ dᵢ})
  (body : ports υ → state_vars υ → ports υ × state_vars υ)
  (well_behaved : ∀ i i' s, ports.correspond_at dᵢ i i' → body i s = body i' s)
  (output_constrained : ∀ i s o, o ∉ dₒ → ((body i s).1.nth o).join = none) 

namespace reaction

  variables {υ : Type*} [decidable_eq υ]

  instance coe_to_fun : has_coe_to_fun (reaction υ) :=
    ⟨_, (λ r, r.body)⟩

  noncomputable instance dec_eq : decidable_eq (reaction υ) := 
    classical.dec_eq _

  -- The proposition, that a given reaction fires on a given port map. This is only defined when
  -- the dimensions of the given port map match the reaction's input dimensions (`r.nᵢ`).
  def fires_on (r : reaction υ) (p : ports υ) : Prop :=
    ∃ (t : {x // x ∈ r.dᵢ}) (_ : t ∈ r.triggers) (v : υ), p.nth t = some v

  noncomputable instance dec_fires_on (r : reaction υ) (p : ports υ) : decidable (r.fires_on p) := 
    classical.prop_decidable _

  lemma eq_fires_on_corr_input (r : reaction υ) (p p' : ports υ) (h : ports.correspond_at r.dᵢ p p') :
    r.fires_on p ↔ r.fires_on p' :=
    begin
      unfold fires_on,
      unfold ports.correspond_at at h,
      split
        ; {
          intro e,
          obtain ⟨t, r, v, h'⟩ := e,
          existsi t,
          existsi r,
          existsi v,
          finish,
        }
    end

  -- A reaction will never fire on empty ports.
  lemma no_in_no_fire (r : reaction υ) : 
    ∀ n : ℕ, ¬ r.fires_on (ports.empty υ n) := 
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

  lemma output_ports_sub_dₒ (rcn : reaction υ) :
    ∀ i s, (rcn i s).1.inhabited_indices.to_finset ⊆ rcn.dₒ :=
    begin
      intros i s,
      simp [(⊆)],
      intro o,
      suffices h : o ∉ rcn.dₒ → o ∉ (rcn i s).fst.inhabited_indices, from not_imp_not.mp h,
      intro h,
      apply ports.inhabited_indices_excl,
      exact rcn.output_constrained i s _ h
    end

end reaction