import mathlib
import inst.primitives
import inst.reaction
open reactor
open reaction

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

@[ext]
structure reactor :=
  (input : ports υ)
  (output : ports υ)
  (state : state_vars υ)
  (priorities : finset ℕ)
  (reactions : ℕ → reaction υ)

namespace reactor 

  variables {υ}

  -- Reactions' equality is non-constructively decidable.
  noncomputable instance : decidable_eq (reactor υ) := classical.dec_eq _

  -- A reaction is a member of a reactor if the reactor contains an ID that maps to it.
  instance rcn_mem : has_mem (reaction υ) (reactor υ) := 
    {mem := λ rcn rtr, ∃ p ∈ rtr.priorities, rtr.reactions p = rcn}

  -- Reactors are equivalent if they are structurally the same.
  instance equiv : has_equiv (reactor υ) := 
    ⟨λ rtr rtr', rtr.priorities = rtr'.priorities ∧ rtr.reactions = rtr'.reactions⟩

  -- Reactor equivalence is reflexive.
  @[refl] 
  lemma equiv_refl (rtr : reactor υ) : rtr ≈ rtr := by simp [(≈)]

  -- Reactor equivalence is symmetric.
  @[symm]
  lemma equiv_symm {rtr rtr' : reactor υ} (h : rtr ≈ rtr') : rtr' ≈ rtr :=
    by { simp [(≈)] at ⊢ h, tauto }

  -- Reactor equivalence is transitive.
  @[trans]
  lemma equiv_trans {rtr₁ rtr₂ rtr₃ : reactor υ} (h₁₂ : rtr₁ ≈ rtr₂) (h₂₃ : rtr₂ ≈ rtr₃) : 
    rtr₁ ≈ rtr₃ :=
    begin 
      simp [(≈)] at ⊢ h₁₂ h₂₃,
      split,
        exact eq.trans h₁₂.left  h₂₃.left,
        exact eq.trans h₁₂.right h₂₃.right
    end

  -- Returns the value of a given port.
  def port (rtr : reactor υ) : ports.role → ℕ → option υ
    | ports.role.input p := rtr.input.nth p
    | ports.role.output p := rtr.output.nth p

  -- Updates a given port in the reactor, to hold a given value.
  def update (rtr : reactor υ) : ports.role → ℕ → option υ → reactor υ
    | ports.role.input  p v := {input  := rtr.input.update_nth p v,  ..rtr}
    | ports.role.output p v := {output := rtr.output.update_nth p v, ..rtr}

  -- Updating a reactor's port with the value it alread has, produces the same reactor.
  @[simp]
  lemma update_self_eq (rtr : reactor υ) (r : ports.role) (p : ℕ) : 
    rtr.update r p (rtr.port r p) = rtr :=
    begin
      induction r ; {
        simp only [update, port, ports.nth],
        rw list.update_nth_same,
        ext ; refl
      }
    end 

  -- All values that are not updated stay the same.
  @[simp]
  lemma update_ne (rtr : reactor υ) (r : ports.role) {p p' : ℕ} (v : option υ) (h : p ≠ p') :
    (rtr.update r p v).port r p' = rtr.port r p' :=
    by cases r ; simp only [update, port, ports.nth, list.nth_update_nth_ne _ _ h]

  -- Updating a reactor's port produces an equivalent reactor.
  lemma update_equiv (rtr : reactor υ) (r : ports.role) (p : ℕ) (v : option υ) :
    rtr.update r p v ≈ rtr :=
    by induction r ; simp [(≈), update]

  -- Updating different ports of a reactor is commutative.
  lemma update_comm (rtr : reactor υ) {p p' : ℕ} (r : ports.role) (v v' : option υ) (h : p ≠ p') :
    (rtr.update r p v).update r p' v' = (rtr.update r p' v').update r p v :=
    begin
      induction r ; {
        simp only [update],
        repeat { split },
        exact list.update_nth_comm _ _ _ h
      }
    end

  -- Two reactors are equal relative to a reaction, if they only differ by the values 
  -- of input ports which are not an input-dependency of the reaction.
  inductive eq_rel_to (rcn : ℕ) : reactor υ → reactor υ → Prop
    | single {p : ℕ} {v : option υ} {rtr rtr' : reactor υ}: (rtr' = rtr.update ports.role.input p v) → (p ∉ (rtr.reactions rcn).dᵢ) → eq_rel_to rtr rtr'
    | multiple {p : ℕ} {v : option υ} {rtr rtrₘ rtr' : reactor υ} : (eq_rel_to rtrₘ rtr) → (rtr' = rtrₘ.update ports.role.input p v) → (p ∉ (rtr.reactions rcn).dᵢ) → eq_rel_to rtr rtr'

  notation r =i= s := (eq_rel_to i r s)

  -- Relative reactor equality implies reactor equivalence. 
  lemma eq_rel_to_equiv {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') : rtr ≈ rtr' := 
    begin
      induction h,
        case eq_rel_to.single {
          have hₑ, from update_equiv h_rtr ports.role.input h_p h_v,
          rw ←h_ᾰ at hₑ,
          symmetry,
          exact hₑ
        },
        case eq_rel_to.multiple {
          have hₑ, from update_equiv h_rtrₘ ports.role.input h_p h_v,
          rw ←h_ᾰ_1 at hₑ,
          symmetry,
          transitivity,
            exact hₑ,
            exact h_ih
        }
    end

  -- Relative reactor equality is reflexive. 
  lemma eq_rel_to_refl (rtr : reactor υ) (rcn : ℕ) : rtr =rcn= rtr := 
    begin
      obtain ⟨p, hₚ⟩ := infinite.exists_not_mem_finset (rtr.reactions rcn).dᵢ, 
      have h, from symm (update_self_eq rtr ports.role.input p),
      exact eq_rel_to.single h hₚ
    end

  -- Relative reactor equality is symmetric. 
  lemma eq_rel_to_symm (rtr rtr' : reactor υ) (rcn : ℕ) (h : rtr =rcn= rtr') :
    rtr' =rcn= rtr := 
    sorry

  -- Relative reactor equality is transitive. 
  lemma eq_rel_to_trans (rtr₁ rtr₂ rtr₃ : reactor υ) (rcn : ℕ) (h₁₂ : rtr₁ =rcn= rtr₂) (h₂₃ : rtr₂ =rcn= rtr₃) :
    rtr₁ =rcn= rtr₃ := 
    sorry

  -- Relatively equal reactors must correspond on all ports that are part of the 
  -- associated reaction's input-dependencies.
  lemma eq_rel_to_eq_dᵢ {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    rtr.input =(rtr.reactions rcn).dᵢ= rtr'.input :=
    begin 
      unfold ports.eq_at,
      intros x hₓ,
      induction h,
        case eq_rel_to.single {
          have hₙ, from ne_of_mem_of_not_mem hₓ h_ᾰ_1,
          have hₑ, from update_ne h_rtr ports.role.input h_v (ne.symm hₙ),
          repeat { rw port at hₑ },
          rw ←h_ᾰ at hₑ,
          exact symm hₑ
        },
        case eq_rel_to.multiple {
          have hₙ, from ne_of_mem_of_not_mem hₓ h_ᾰ_2,
          rw ←(eq_rel_to_equiv h_ᾰ).right at hₓ,
          have hᵢ, from h_ih hₓ,
          have hₑ, from update_ne h_rtrₘ ports.role.input h_v (ne.symm hₙ),
          repeat { rw port at hₑ },
          rw ←h_ᾰ_1 at hₑ,
          symmetry,
          transitivity,
            exact hₑ,
            exact hᵢ
        }
    end
   
  -- Returns the result of merging given state and output ports into a reactor.
  def merge (rtr : reactor υ) (os : ports υ × state_vars υ) : reactor υ :=
    {output := rtr.output.merge os.1, state := os.2, ..rtr}

  -- Merging data into a reactor produces an equivalent reactor.
  lemma merge_equiv (rtr : reactor υ) (os : ports υ × state_vars υ) : rtr.merge os ≈ rtr :=
    by simp [(≈), merge]

  -- Returns the reactor that we get by running a given reaction and merging its outputs into the reactor.
  noncomputable def run (rtr : reactor υ) (rcn : ℕ) : reactor υ :=
    if (rtr.reactions rcn).fires_on rtr.input 
    then rtr.merge ((rtr.reactions rcn) rtr.input rtr.state)
    else rtr

  -- Running a reactor does not change its input.
  lemma run_eq_input (rtr : reactor υ) (rcn : ℕ) : (rtr.run rcn).input = rtr.input :=
    begin
      unfold run merge,
      by_cases h : (rtr.reactions rcn).fires_on rtr.input,
        simp [if_pos h],
        simp [if_neg h]
    end

  -- Running relatively equal reactors produces relatively equal reactors.
  lemma run_eq_rel_to (rtr rtr' : reactor υ) (rcn : ℕ) (h : rtr =rcn= rtr') :
    (rtr.run rcn) =rcn= (rtr'.run rcn) :=
    begin
      have hᵣ : (rtr.reactions rcn) rtr.input = (rtr'.reactions rcn) rtr'.input,
      by {

      }
    end

  lemma run_equiv (rtr : reactor υ) (rcn : ℕ) : 
    rtr ≈ rtr.run rcn :=
    begin
      unfold run,
      by_cases h : (rtr.reactions rcn_id).fires_on rtr.input
        ; simp [merge, h, (≈)]
    end

  lemma run_affected_ports_sub_dₒ (rtr : reactor υ) (rcn_id : ℕ) :
    (rtr.run rcn_id).2.to_finset ⊆ (rtr.reactions rcn_id).dₒ :=
    begin
      unfold run,
      by_cases h_c : ((rtr.reactions rcn_id).fires_on rtr.input),
        simp [if_pos h_c, run_aux, reaction.outputs_sub_dₒ],
        simp [if_neg h_c]
    end

  theorem eq_rel_to_rcn_run (rtr rtr' : reactor υ) (rcn_id : ℕ) : 
    rtr.eq_rel_to rtr' rcn_id → (rtr.run rcn_id).1.eq_rel_to (rtr'.run rcn_id).1 rcn_id ∧ (rtr.run rcn_id).2 = (rtr'.run rcn_id).2 :=
    begin
      intro h,
      simp [eq_rel_to, (≈)] at h,
      unfold run run_aux,
      have h_f, from reaction.eq_input_eq_fires h.2.2.2,
      have h_w : (rtr.reactions rcn_id) rtr.input rtr'.state = (rtr.reactions rcn_id) rtr'.input rtr'.state,
      from (rtr.reactions rcn_id).in_con _ _ _ h.2.2.2,
      rw [h.2.2.1, ←h.1.1, h_w, h.1.2, h.2.1],
      by_cases hᵢ : (rtr'.reactions rcn_id).fires_on rtr.input,
        {
          rw if_pos hᵢ,
          rw ←h.1.2 at hᵢ ⊢,
          rw if_pos (h_f.mp hᵢ),
          simp,
          unfold eq_rel_to,
            repeat { split },
            exact h.2.2.2
        },
        {
          rw if_neg hᵢ,
          rw h.1.2 at h_f,
          rw if_neg ((not_iff_not_of_iff h_f).mp hᵢ),
          simp,
          unfold eq_rel_to,
          exact h
        }
    end

end reactor
