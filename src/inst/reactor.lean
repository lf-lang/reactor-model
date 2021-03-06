import inst.reaction
import tactic
open reactor
open reactor.ports

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
    | role.input := rtr.input.nth
    | role.output := rtr.output.nth

  -- Updates a given port in the reactor, to hold a given value.
  def update (rtr : reactor υ) : ports.role → ℕ → option υ → reactor υ
    | role.input  p v := {input  := rtr.input.update_nth p v,  ..rtr}
    | role.output p v := {output := rtr.output.update_nth p v, ..rtr}

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
  @[simp]
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

  -- Updating a reactor's port does not change the reactions.
  @[simp]
  lemma update_reactions_eq (rtr : reactor υ) (r : ports.role) (p : ℕ) (v : option υ) :
    (rtr.update r p v).reactions = rtr.reactions :=
    (update_equiv rtr r p v).right

  -- Updating a reactor's port does not change the priorities.
  @[simp]
  lemma update_priorities_eq (rtr : reactor υ) (r : ports.role) (p : ℕ) (v : option υ) :
    (rtr.update r p v).priorities = rtr.priorities :=
    (update_equiv rtr r p v).left

  -- Updating a reactor's port does not change the state.
  @[simp]
  lemma update_state_eq (rtr : reactor υ) (r : ports.role) (p : ℕ) (v : option υ) :
    (rtr.update r p v).state = rtr.state :=
    by cases r ; simp [update]

  -- Updating a reactor's input/output ports does not change its output/input ports.
  @[simp]
  lemma update_ports_eq (rtr : reactor υ) (r : ports.role) (p : ℕ) (v : option υ) :
    (rtr.update r p v).port r.opposite = rtr.port r.opposite :=
    begin
      cases r ; {
        simp [update, ports.role.opposite],
        ext,
        split ; simp [port]
      }
    end

  -- Updating the same port twice makes the first update irrelevant.
  @[simp]
  lemma update_same (rtr : reactor υ) (r : ports.role) (p : ℕ) (v v' : option υ) :
    (rtr.update r p v).update r p v' = rtr.update r p v' :=
    by cases r ; simp [update, list.update_same]

  -- If changing on port gets us from one reactor to another, then we can also do this in reverse.
  lemma update_symm {rtr rtr' : reactor υ} {r : ports.role} {p : ℕ} {v : option υ} (h : rtr = rtr'.update r p v) :
    rtr' = rtr.update r p (rtr'.port r p) :=
    by cases r ; simp [h, update_same, update_self_eq]

  -- Two reactors are equal relative to a reaction, if they only differ by the values 
  -- of input ports which are not an input-dependency of the reaction.
  inductive eq_rel_to (rcn : ℕ) : reactor υ → reactor υ → Prop
    | single {p : ℕ} {v : option υ} {rtr rtr' : reactor υ}: (rtr' = rtr.update role.input p v) → (p ∉ (rtr.reactions rcn).deps role.input) → eq_rel_to rtr rtr'
    | multiple {rtr rtrₘ rtr' : reactor υ} : (eq_rel_to rtr rtrₘ) → (eq_rel_to rtrₘ rtr') → eq_rel_to rtr rtr'

  notation r =i= s := (eq_rel_to i r s)

  -- Relative reactor equality implies reactor equivalence. 
  lemma eq_rel_to_equiv {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') : rtr ≈ rtr' := 
    begin
      induction h,
        case eq_rel_to.single {
          have hₑ, from update_equiv h_rtr role.input h_p h_v,
          rw ←h_ᾰ at hₑ,
          symmetry,
          exact hₑ
        },
        case eq_rel_to.multiple {
          transitivity,
            exact h_ih_ᾰ,
            exact h_ih_ᾰ_1
        }
    end

  -- Relative reactor equality is reflexive. 
  lemma eq_rel_to_refl (rtr : reactor υ) (rcn : ℕ) : rtr =rcn= rtr := 
    begin
      obtain ⟨p, hₚ⟩ := infinite.exists_not_mem_finset (rtr.reactions rcn).dᵢ, 
      have h, from symm (update_self_eq rtr role.input p),
      exact eq_rel_to.single h hₚ
    end

  -- Relative reactor equality is symmetric. 
  lemma eq_rel_to_symm {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    rtr' =rcn= rtr := 
    begin
      induction h,
        case eq_rel_to.single {
          have h, from eq_rel_to.single h_ᾰ h_ᾰ_1,
          rw (eq_rel_to_equiv h).right at h_ᾰ_1,
          exact eq_rel_to.single (update_symm h_ᾰ) h_ᾰ_1
        },
        case eq_rel_to.multiple {
          exact eq_rel_to.multiple h_ih_ᾰ_1 h_ih_ᾰ
        }
    end

  -- Relatively equal reactors have the same state.
  lemma eq_rel_to_eq_state {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    rtr.state = rtr'.state :=
    begin
      induction h,
        case eq_rel_to.single {
          rw [←(update_state_eq h_rtr role.input h_p h_v), h_ᾰ],
        },
        case eq_rel_to.multiple {
          transitivity,
            exact h_ih_ᾰ,
            exact h_ih_ᾰ_1
        }
    end

  -- Relatively equal reactors have the same output.
  lemma eq_rel_to_eq_output {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    rtr.output = rtr'.output :=
    begin
      induction h,
        case eq_rel_to.single {
          have h', from update_ports_eq h_rtr role.input h_p h_v,
          rw [ports.role.opposite, ←h_ᾰ, port, port] at h',
          have hₗ : h_rtr.output.length = h_rtr'.output.length, by simp only [update, h_ᾰ],
          exact ports.ext (symm h') hₗ
        },
        case eq_rel_to.multiple {
          transitivity,
            exact h_ih_ᾰ,
            exact h_ih_ᾰ_1
        }
    end

  -- Relatively equal reactors must correspond on all ports that are part of the 
  -- associated reaction's input-dependencies.
  lemma eq_rel_to_eq_at_dᵢ {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    rtr.input =(rtr.reactions rcn).dᵢ= rtr'.input :=
    begin 
      unfold ports.eq_at,
      intros x hₓ,
      induction h,
        case eq_rel_to.single {
          have hₙ, from ne_of_mem_of_not_mem hₓ h_ᾰ_1,
          have hₑ, from update_ne h_rtr role.input h_v (ne.symm hₙ),
          repeat { rw port at hₑ },
          rw ←h_ᾰ at hₑ,
          exact symm hₑ
        },
        case eq_rel_to.multiple {
          have h, from h_ih_ᾰ hₓ,
          rw (eq_rel_to_equiv h_ᾰ).right at hₓ,
          have h', from h_ih_ᾰ_1 hₓ,
          transitivity,
            exact h,
            exact h'
        }
    end

  -- For relatively equal reactors, either both or neither fire the relevant reaction.
  lemma eq_rel_to_fire_iff {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    (rtr.reactions rcn).fires_on rtr.input ↔ (rtr'.reactions rcn).fires_on rtr'.input :=
    begin
      unfold reaction.fires_on,
      have hₑ, from eq_rel_to_equiv h,
      have hd, from eq_rel_to_eq_at_dᵢ h,
      repeat { rw hₑ.right at hd ⊢ },
      split, 
      all_goals {
        intro h',
        obtain ⟨t, hₜ, v, hᵥ⟩ := h',
        existsi t,
        existsi hₜ,
        existsi v,
        unfold ports.eq_at at hd,
        have hd', from hd t t.property,
        rw hᵥ at hd'
      },
      exact symm hd',
      exact hd',
    end
   
  -- Returns the result of merging given state and output ports into a reactor.
  def merge (rtr : reactor υ) (os : ports υ × state_vars υ) : reactor υ :=
    {output := rtr.output.merge os.1, state := os.2, ..rtr}

  -- If the inhabited indices of a given reaction output assignment are a subset of some set `dₒ`,
  -- then merging that output into a reactor can only produce output-port differences at ports from `dₒ`.
  lemma merge_inhabited_eq_diff (rtr : reactor υ) {os : ports υ × state_vars υ} {dₒ : finset ℕ} (h : os.1.inhabited_indices ⊆ dₒ) : 
    (rtr.output.index_diff (rtr.merge os).output) ⊆ dₒ :=
    begin
      unfold merge,
      transitivity,
        exact ports.merge_index_diff_sub_inhabited rtr.output os.1,
        exact h
    end

  -- Merging the same data into relatively equal reactors, produces relatively equal reactors.
  lemma merge_eq_rel_to {rtr rtr' : reactor υ} {rcn : ℕ} {os : ports υ × state_vars υ} (h : rtr =rcn= rtr') :
    (rtr.merge os) =rcn= (rtr'.merge os) :=
    begin
      unfold merge,
      rw [←eq_rel_to_eq_output h, ←(eq_rel_to_equiv h).left, ←(eq_rel_to_equiv h).right],
      induction h,
        case eq_rel_to.single {
          have hᵢ : h_rtr'.input = h_rtr.input.update_nth h_p h_v, by finish,
          rw hᵢ,
          exact eq_rel_to.single (refl _) h_ᾰ_1        
        },
        case eq_rel_to.multiple {
          rw [←eq_rel_to_eq_output h_ᾰ, ←(eq_rel_to_equiv h_ᾰ).left, ←(eq_rel_to_equiv h_ᾰ).right] at h_ih_ᾰ_1,
          exact eq_rel_to.multiple h_ih_ᾰ h_ih_ᾰ_1           
        }
    end

  -- Merging data into a reactor produces an equivalent reactor.
  @[simp]
  lemma merge_equiv (rtr : reactor υ) (os : ports υ × state_vars υ) : rtr.merge os ≈ rtr :=
    by simp [(≈), merge]

  -- Returns the reactor that we get by running a given reaction and merging its outputs into the reactor.
  noncomputable def run (rtr : reactor υ) (rcn : ℕ) : reactor υ :=
    if (rtr.reactions rcn).fires_on rtr.input 
    then rtr.merge ((rtr.reactions rcn) rtr.input rtr.state)
    else rtr

  -- Running a reactor does not change its input.
  @[simp]
  lemma run_eq_input (rtr : reactor υ) (rcn : ℕ) : (rtr.run rcn).input = rtr.input :=
    begin
      unfold run merge,
      by_cases h : (rtr.reactions rcn).fires_on rtr.input,
        simp [if_pos h],
        simp [if_neg h]
    end

  -- Running the reaction relative to which two reactors are equal, produces the same output.
  lemma run_rcn_eq_rel_to {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    (rtr.reactions rcn) rtr.input rtr.state = (rtr'.reactions rcn) rtr'.input rtr'.state :=
    begin
      rw eq_rel_to_eq_state h,
      have h', from (eq_rel_to_eq_at_dᵢ h),
      rw (eq_rel_to_equiv h).right at h' ⊢, 
      exact (rtr'.reactions rcn).in_con _ h'
    end

  -- Running relatively equal reactors produces relatively equal reactors.
  theorem run_eq_rel_to {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    (rtr.run rcn) =rcn= (rtr'.run rcn) :=
    begin
      unfold run,
      by_cases hf : (rtr.reactions rcn).fires_on rtr.input,
        {
          rw if_pos hf,
          rw eq_rel_to_fire_iff h at hf,
          rw [if_pos hf, run_rcn_eq_rel_to h],
          exact merge_eq_rel_to h
        },
        {
          rw if_neg hf,
          rw eq_rel_to_fire_iff h at hf,
          rw if_neg hf,
          exact h
        }
    end

  -- Running a reactor produces an equivalent reactor.
  @[simp]
  lemma run_equiv (rtr : reactor υ) (rcn : ℕ) : rtr.run rcn ≈ rtr :=
    begin
      unfold run,
      by_cases hf : (rtr.reactions rcn).fires_on rtr.input,
        simp [if_pos hf],
        simp [if_neg hf]
    end

  -- Updating an input port that is independent of a reaction can be done before or after running that reaction,
  -- without changing the resulting reactor.
  lemma run_update_input_comm {rtr : reactor υ} {rcn : ℕ} {i : ℕ} (v : option υ) (h : i ∉ (rtr.reactions rcn).dᵢ) :
    (rtr.run rcn).update role.input i v = (rtr.update role.input i v).run rcn :=
    begin
      have hᵣ, from eq_rel_to.single (refl (rtr.update role.input i v)) h,
      replace hᵣ := run_eq_rel_to hᵣ,
      have hₑ, from equiv_trans (update_equiv (rtr.run rcn) role.input i v) (run_equiv rtr rcn),
      rw ←hₑ.right at h,
      have hₗ, from eq_rel_to.single (refl ((rtr.run rcn).update role.input i v)) h,
      replace hₗ := eq_rel_to_symm hₗ,
      have h', from eq_rel_to.multiple hₗ hᵣ,
      ext1,
        simp [update],
        exact eq_rel_to_eq_output h',
        exact eq_rel_to_eq_state h',
        exact (eq_rel_to_equiv h').left,
        exact (eq_rel_to_equiv h').right
    end

  -- Updating multiple input ports that are independent of a reaction can be done before or after running that reaction,
  -- without changing the resulting reactor.
  lemma run_update_inputs_comm {rtr rtr' : reactor υ} {rcn : ℕ} (h : rtr =rcn= rtr') :
    {reactor . input := rtr'.input, ..(rtr.run rcn)} = rtr'.run rcn :=
    begin
      induction h,
        case eq_rel_to.single {
          rw [h_ᾰ, ←(run_eq_input _ rcn), ←(run_update_input_comm h_v h_ᾰ_1)],
          refl
        },
        case eq_rel_to.multiple {
          cases h_rtrₘ.run rcn,
          injection h_ih_ᾰ,
          rw [←h_2, ←h_3, ←h_4, ←h_5] at h_ih_ᾰ_1,
          exact h_ih_ᾰ_1
        }
    end

  -- Any ports that change from running a reaction in a reactor, have to be part
  -- of the reaction's output-dependencies. I.e. the set index-diff of the output
  -- has to be a subset of the reaction's `dₒ`. 
  lemma run_out_diff_sub_dₒ (rtr : reactor υ) (rcn : ℕ) : 
    rtr.output.index_diff (rtr.run rcn).output ⊆ (rtr.reactions rcn).dₒ :=
    begin 
      unfold run,
      by_cases hf : (rtr.reactions rcn).fires_on rtr.input,
        {
          rw if_pos hf,
          have hₛ, from reaction.outputs_sub_dₒ (rtr.reactions rcn) rtr.input rtr.state,
          exact merge_inhabited_eq_diff rtr hₛ,
        },
        simp [if_neg hf, ports.index_diff_eq_ports_empty (refl rtr.output)]
    end

end reactor