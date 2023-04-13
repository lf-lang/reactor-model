import ReactorModel.Determinism.InstantaneousExecution

namespace Execution

open ReactorType
open State (Closed)

variable [Proper α] {s s₁ s₂ : State α} [State.Nontrivial s] [State.Nontrivial s₁] in section

namespace AdvanceTag

theorem not_Closed (a : s₁ ⇓- s₂) : ¬(Closed s₂) :=
  have := a.advance.preserves_Nontrivial -- TODO: Make this work via type class inference.
  (·.progress_Nonempty.ne_empty a.advance.progress_empty)

theorem nonrepeatable (a₁ : s₁ ⇓- s₂) (a₂ : s₂ ⇓- s₃) : False :=
  a₁.not_Closed a₂.closed

theorem tag_lt (a : s₁ ⇓- s₂) : s₁.tag < s₂.tag :=
  a.advance.tag_lt

theorem tag_ne (a : s₁ ⇓- s₂) : s₁.tag ≠ s₂.tag :=
  ne_of_lt a.tag_lt

theorem deterministic (a₁ : s ⇓- s₁) (a₂ : s ⇓- s₂) : s₁ = s₂ :=
  a₁.advance.deterministic a₂.advance

instance preserves_Nontrivial [State.Nontrivial s₁] {e : s₁ ⇓- s₂} : State.Nontrivial s₂ :=
  e.advance.preserves_Nontrivial

end AdvanceTag

namespace Instantaneous
namespace ClosedExecution

theorem not_Closed (e : s₁ ⇓| s₂) : ¬(Closed s₁) := by
  sorry
  /-simp [Closed]
  have h := Partial.Nonempty.iff_ids_nonempty.mp $ State.Nontrivial.nontrivial (s := s₁)
  exact e.fresh ▸ h.ne_empty.symm 
  -/

theorem acyclic (e : s₁ ⇓| s₂) (h : rcn ∈ e.rcns) : rcn ≮[s₁.rtr] rcn :=
  e.exec.acyclic h

theorem preserves_tag (e : s₁ ⇓| s₂) : s₁.tag = s₂.tag :=
  e.exec.preserves_tag

theorem equiv (e : s₁ ⇓| s₂) : s₁.rtr ≈ s₂.rtr :=
  e.exec.equiv
  
theorem rcns_Nodup (e : s₁ ⇓| s₂) : e.rcns.Nodup := 
  e.exec.rcns_nodup

theorem progress_def (e : s₁ ⇓| s₂) : s₂.progress = s₁.rtr[.rcn].ids :=
  Equivalent.obj?_rcn_eq e.equiv ▸ e.closed

theorem mem_rcns_iff (e : s₁ ⇓| s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₁.rtr[.rcn] ∧ rcn ∉ s₁.progress) := by
  simp [Partial.mem_def, e.progress_def ▸ e.exec.mem_rcns_iff (rcn := rcn)]

theorem progress_empty_mem_rcns_iff (e : s₁ ⇓| s₂) (h : s₁.progress = ∅) : 
    (rcn ∈ e.rcns) ↔ rcn ∈ s₁.rtr[.rcn] := by
  simp [e.mem_rcns_iff, h]

theorem rcns_perm (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : e₁.rcns ~ e₂.rcns := by
  simp [List.perm_ext e₁.rcns_Nodup e₂.rcns_Nodup, e₁.mem_rcns_iff, e₂.mem_rcns_iff]

theorem tag_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.tag = s₂.tag :=
  e₁.exec.preserves_tag ▸ e₂.exec.preserves_tag

theorem progress_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.progress = s₂.progress := by
  simp [e₁.progress_def, e₂.progress_def]

theorem step_determined (e : s ⇓| s₁) (a : s ⇓- s₂) : False :=
  e.not_Closed a.closed

instance preserves_Nontrivial [h : State.Nontrivial s₁] {e : s₁ ⇓| s₂} : State.Nontrivial s₂ where
  nontrivial := Equivalent.obj?_rcn_eq e.equiv ▸ h.nontrivial

theorem nonrepeatable (e₁ : s₁ ⇓| s₂) (e₂ : s₂ ⇓| s₃) : False :=
  have := e₁.preserves_Nontrivial -- TODO: Make this work via type class inference.
  e₂.not_Closed e₁.closed

theorem progress_ssubset (e : s₁ ⇓| s₂) : s₁.progress ⊂ s₂.progress := by
  sorry
  /-have := e.preserves_Nontrivial -- TODO: Make this work via type class inference.
  rw [e.fresh]
  exact e.closed.progress_Nonempty.empty_ssubset
  -/

end ClosedExecution
end Instantaneous

namespace Step

theorem tag_le : (s₁ ⇓ s₂) → s₁.tag ≤ s₂.tag
  | close e   => le_of_eq e.preserves_tag
  | advance a => le_of_lt a.tag_lt

theorem seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | close e₁,   close e₂   => e₁.nonrepeatable e₂ |>.elim
  | advance a₁, advance a₂ => a₁.nonrepeatable a₂ |>.elim
  | close e,    advance a  => e.preserves_tag ▸ a.tag_lt
  | advance a,  close e    => e.preserves_tag ▸ a.tag_lt

instance preserves_Nontrivial [State.Nontrivial s₁] : (s₁ ⇓ s₂) → State.Nontrivial s₂
  | close e   => e.preserves_Nontrivial
  | advance a => a.preserves_Nontrivial

theorem resolve_close : (e : s₁ ⇓ s₂) → ¬s₁.Closed → Nonempty (s₁ ⇓| s₂)
  | close e  , _ => ⟨e⟩
  | advance a, h => absurd a.closed h

end Step

end

variable [Proper α] {s s₁ s₂ : State α} [State.Nontrivial s] [State.Nontrivial s₁]

theorem Instantaneous.ClosedExecution.deterministic (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec (e₁.tag_eq e₂) (e₁.progress_eq e₂)

theorem Step.deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.deterministic a₂
  | close e, advance a | advance a, close e => e.step_determined a |>.elim

end Execution