import ReactorModel.Determinism.ExecutionStep

open ReactorType Classical

namespace Execution

variable [Practical α] {s s₁ s₂ : State α}

namespace State

def Nontrivial (s : State α) : Prop :=
  s.rtr[.rcn].Nonempty

theorem Nontrivial.equiv (e : s₁.rtr ≈ s₂.rtr) (n : s₁.Nontrivial) : s₂.Nontrivial := by
  simp_all [Nontrivial, Equivalent.obj?_rcn_eq e]

theorem Closed.progress_nonempty (n : s.Nontrivial) (h : Closed s) : s.progress.Nonempty := by
  simp_all [Closed, ←Partial.Nonempty.iff_ids_nonempty]
  exact n

theorem Advance.preserves_nontrivial (n : Nontrivial s₁) : (Advance s₁ s₂) → s₂.Nontrivial
  | ⟨_, c⟩ => n.equiv c.equiv

end State

namespace AdvanceTag

theorem not_closed (a : s₁ ⇓- s₂) (n : s₁.Nontrivial) : ¬s₂.Closed :=
  (·.progress_nonempty (a.advance.preserves_nontrivial n) |>.ne_empty a.advance.progress_empty)

theorem nonrepeatable (a₁ : s₁ ⇓- s₂) (a₂ : s₂ ⇓- s₃) (n : s₁.Nontrivial) : False :=
  a₁.not_closed n a₂.closed

instance preserves_nontrivial {e : s₁ ⇓- s₂} (n : s₁.Nontrivial) : s₂.Nontrivial :=
  e.advance.preserves_nontrivial n

end AdvanceTag

theorem Instantaneous.ClosedExecution.preserves_nontrivial {e : s₁ ⇓| s₂} (n : s₁.Nontrivial) : 
    s₂.Nontrivial := by
  simp_all [State.Nontrivial, Equivalent.obj?_rcn_eq e.equiv]

namespace Step

theorem seq_tag_lt (n : s₁.Nontrivial) : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | close e₁,   close e₂   => e₁.nonrepeatable e₂ |>.elim
  | advance a₁, advance a₂ => a₁.nonrepeatable a₂ n |>.elim
  | close e,    advance a  => e.preserves_tag ▸ a.tag_lt
  | advance a,  close e    => e.preserves_tag ▸ a.tag_lt

instance preserves_nontrivial (n : s₁.Nontrivial) : (s₁ ⇓ s₂) → s₂.Nontrivial
  | close e   => e.preserves_nontrivial n
  | advance a => a.preserves_nontrivial n

end Step

-- TODO: This doesn't require nontrivial.
theorem tag_le {s₁ s₂ : State α} (e : s₁ ⇓* s₂) : s₁.tag ≤ s₂.tag := by
  induction e with
  | refl        => exact le_refl _
  | step e _ hi => exact le_trans e.tag_le hi

theorem seq_progress_ssubset_or_tag_lt (n : s₁.Nontrivial) : 
    (s₁ ⇓ s₂) → (s₂ ⇓* s₃) → (s₁.progress ⊂ s₃.progress) ∨ (s₁.tag < s₃.tag)
  | e₁₂,        step e e' => .inr $ lt_of_lt_of_le (e₁₂.seq_tag_lt n e) e'.tag_le
  | .close e,   refl      => .inl $ e.progress_ssubset
  | .advance a, refl      => .inr $ a.tag_lt

theorem nontrivial_deterministic {s s₁ s₂ : State α} (n : s.Nontrivial)
    (e₁ : s ⇓* s₁) (e₂ : s ⇓* s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : 
    s₁ = s₂ := by
  induction e₁ generalizing s₂ <;> cases e₂
  case refl.refl => rfl
  case step.step e₁ _ hi _ e₂ e₂' =>
    exact hi (e₁.preserves_nontrivial n) (e₁.deterministic e₂ ▸ e₂') ht hp
  all_goals
    have e := ‹_ ⇓ _›; have e' := ‹_ ⇓* _›
    exact match seq_progress_ssubset_or_tag_lt n e e' with
    | .inl h => absurd hp (Set.ssubset_ne $ by simp_all) 
    | .inr h => absurd ht $ ne_of_lt (by simp_all)

end Execution