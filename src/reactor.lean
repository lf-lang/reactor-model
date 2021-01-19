import primitives
import reaction

open reactor
open reaction

-- It would be nice to declare reactors in a similar fashion to reactions.
-- I.e. reactions in themselves declare what they connect to (dᵢ and dₒ).
-- The difference is that reactions themselves are just a single "connection point",
-- so the mapping is a many-to-one (dependencies to reaction).
-- For reactors the mapping would have to be a many to many mapping (other reactors'
-- ports to own ports). This would on the one hand require the number of other reactors
-- to become part of a reactor's type, which seems inelegant. And further the mapping
-- would have to be implemented as a relation between another reactor's ports and the
-- self-reactor's ports. This would in turn also require nᵢ and nₒ to move into a 
-- reactor's type.

structure reactor :=
  (input : ports)
  (output : ports)
  (state : state_vars)
  (priorities : finset ℕ)
  (reactions : ℕ → reaction)

noncomputable instance : decidable_eq reactor := classical.dec_eq _

namespace reactor 

  @[reducible]
  instance mem : has_mem reaction reactor := {mem := λ rcn rtr, ∃ p ∈ rtr.priorities, rtr.reactions p = rcn}

  instance equiv : has_equiv reactor := ⟨λ r r', r.priorities = r'.priorities ∧ r.reactions = r'.reactions⟩

  instance : is_equiv reactor (≈) := 
    {
      symm := begin simp [(≈)], finish end,
      trans := begin simp [(≈)], finish end,
      refl := by simp [(≈)]
    }

  def run (rtr : reactor) (rcn_id : ℕ) : reactor :=
    if (rtr.reactions rcn_id).fires_on rtr.input then
      let os' := (rtr.reactions rcn_id) rtr.input rtr.state in
      {output := os'.1, state := os'.2, ..rtr}
    else 
      rtr

  lemma run_equiv (rtr : reactor) (rcn_id : ℕ) : 
    rtr ≈ rtr.run rcn_id :=
    begin
      unfold run,
      by_cases (rtr.reactions rcn_id).fires_on rtr.input
        ; simp [h, (≈)]
    end

  def update_input (rtr : reactor) (i : ℕ) (v : option value) : reactor :=
    {input := rtr.input.update_nth i v, ..rtr}

  lemma update_input_equiv (rtr : reactor) (i : ℕ) (v : option value) : 
    rtr ≈ rtr.update_input i v :=
    begin
      unfold update_input,
      simp [(≈)]
    end

-- https://leanprover.zulipchat.com/#narrow/stream/217875-Is-there.20code.20for.20X.3F/topic/list.2Eupdate_nth_comm/near/223010209
  @[simp]
  lemma list.update_nth_nil (α : Type) (n : ℕ) (a : α) : [].update_nth n a = [] := rfl
  lemma list.update_nth_comm (α : Type) (a b : α) : Π (n m : ℕ) (h : n ≠ m) (l : list α),
    (l.update_nth n a).update_nth m b =
    (l.update_nth m b).update_nth n a
    | _ _ _ [] := by simp
    | 0 0 h (x :: t) := absurd rfl h
    | (n + 1) 0 h (x :: t) := by simp [list.update_nth]
    | 0 (m + 1) h (x :: t) := by simp [list.update_nth]
    | (n + 1) (m + 1) h (x :: t) := by { simp [list.update_nth], exact list.update_nth_comm n m (λ h', h $ nat.succ_inj'.mpr h') t}

  lemma update_input_comm {i i' : ℕ} (h : i ≠ i') (v v' : option value) (rtr : reactor) :
    (rtr.update_input i v).update_input i' v' = (rtr.update_input i' v').update_input i v :=
    begin
      unfold update_input,
      simp,
      apply list.update_nth_comm _ _ _ _ _ h _,
    end

  noncomputable def priority_of (rtr : reactor) (rcn : reaction) (h : rcn ∈ rtr) : ℕ := 
    h.some

end reactor
