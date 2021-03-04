import data.finset
import inst.primitives
open reactor

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

-- Reactions consist of a set of input dependencies `dᵢ`, output dependencies `dₒ`, `triggers` and
-- a function `body` that transforms a given input port assignment and reactor state to an output
-- port assignment and a new reactor state.
-- To assure correct behavior of the `body`, we add the constraints `in_con` and `out_con`.
structure reaction :=
  (dᵢ : finset ℕ) 
  (dₒ : finset ℕ)
  (triggers : finset {i // i ∈ dᵢ})
  (body : ports υ → state_vars υ → ports υ × state_vars υ)
  (in_con : ∀ {i i'} s, (i =dᵢ= i') → body i s = body i' s)
  (out_con : ∀ i s {o}, o ∉ dₒ → (body i s).1.nth o = none) 

namespace reaction

  variable {υ}

  -- Calling a reaction as function, means calling its body.
  instance coe_to_fun : has_coe_to_fun (reaction υ) := ⟨_, (λ r, r.body)⟩

  -- Reactions' equality is non-constructively decidable.
  noncomputable instance dec_eq : decidable_eq (reaction υ) := classical.dec_eq _

  -- Any port assignment returned by a reaction can only assign values to ports which are part of its output-dependencies.
  -- Hence the inhabited indices of that port assignment must be a subset of the reaction's `dₒ`.
  lemma outputs_sub_dₒ (rcn : reaction υ) (i : ports υ) (s : state_vars υ) :
    (rcn i s).1.inhabited_indices ⊆ rcn.dₒ :=
    begin
      simp only [(⊆)],
      intro o,
      rw ←not_imp_not,
      intro h,
      have hₙ, from rcn.out_con i s h,
      exact ports.inhabited_indices_none hₙ
    end

  -- The proposition, that a given reaction fires on a given port assignment,
  -- i.e. that it should execute if its reaction has the given ports as input ports.
  def fires_on (rcn : reaction υ) (p : ports υ) : Prop :=
    ∃ (t : {x // x ∈ rcn.dᵢ}) (_ : t ∈ rcn.triggers) (v : υ), p.nth t = some v

  noncomputable instance dec_fires_on (rcn : reaction υ) (p : ports υ) : decidable (rcn.fires_on p) := 
    classical.prop_decidable _

  -- If two port assignments are equal relative to a reactions input-dependencies, 
  -- then the reaction fires on one exactly when it fires on the other.
  lemma eq_input_eq_fires {rcn : reaction υ} {p p' : ports υ} (h : p =rcn.dᵢ= p') :
    rcn.fires_on p ↔ rcn.fires_on p' :=
    begin
      simp [fires_on, ports.eq_at] at h ⊢,
      split,
        all_goals { 
          intro hₑ,
          obtain ⟨t, r, v, h'⟩ := hₑ,
          existsi t,
          existsi r,
          existsi v,
          obtain ⟨hₜ, _⟩ := r
        },
        simp [←(h t hₜ), h'],
        simp [h t hₜ, h']
    end

end reaction