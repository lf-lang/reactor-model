import ReactorModel.Determinism.InstantaneousExecution

namespace Execution

open ReactorType
open State (Closed)

variable [Practical α] {s s₁ s₂ : State α}

namespace AdvanceTag

theorem tag_lt (a : s₁ ⇓- s₂) : s₁.tag < s₂.tag :=
  a.advance.tag_lt

theorem tag_ne (a : s₁ ⇓- s₂) : s₁.tag ≠ s₂.tag :=
  ne_of_lt a.tag_lt

theorem deterministic (a₁ : s ⇓- s₁) (a₂ : s ⇓- s₂) : s₁ = s₂ :=
  a₁.advance.deterministic a₂.advance

end AdvanceTag

namespace Instantaneous
namespace ClosedExecution

theorem not_closed (e : s₁ ⇓| s₂) : ¬s₁.Closed := 
  e.exec.not_closed

theorem nonrepeatable (e₁ : s₁ ⇓| s₂) (e₂ : s₂ ⇓| s₃) : False :=
  e₂.not_closed e₁.closed

theorem acyclic (e : s₁ ⇓| s₂) (h : rcn ∈ e.rcns) : rcn ≮[s₁.rtr] rcn :=
  e.exec.acyclic h

theorem preserves_tag (e : s₁ ⇓| s₂) : s₁.tag = s₂.tag :=
  e.exec.preserves_tag

theorem equiv (e : s₁ ⇓| s₂) : s₁.rtr ≈ s₂.rtr :=
  e.exec.equiv
  
theorem rcns_nodup (e : s₁ ⇓| s₂) : e.rcns.Nodup := 
  e.exec.rcns_nodup

theorem progress_def (e : s₁ ⇓| s₂) : s₂.progress = s₁.rtr[.rcn].ids :=
  Equivalent.obj?_rcn_eq e.equiv ▸ e.closed

theorem mem_rcns_iff (e : s₁ ⇓| s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₁.rtr[.rcn] ∧ rcn ∉ s₁.progress) := by
  simp [Partial.mem_def, e.progress_def ▸ e.exec.mem_rcns_iff (rcn := rcn)]

theorem progress_empty_mem_rcns_iff (e : s₁ ⇓| s₂) (h : s₁.progress = ∅) : 
    (rcn ∈ e.rcns) ↔ rcn ∈ s₁.rtr[.rcn] := by
  simp [e.mem_rcns_iff, h]

theorem rcns_perm (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : e₁.rcns ~ e₂.rcns := by
  simp [List.perm_ext e₁.rcns_nodup e₂.rcns_nodup, e₁.mem_rcns_iff, e₂.mem_rcns_iff]

theorem tag_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.tag = s₂.tag :=
  e₁.exec.preserves_tag ▸ e₂.exec.preserves_tag

theorem progress_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.progress = s₂.progress := by
  simp [e₁.progress_def, e₂.progress_def]

theorem step_determined (e : s ⇓| s₁) (a : s ⇓- s₂) : False :=
  e.not_closed a.closed

theorem progress_ssubset (e : s₁ ⇓| s₂) : s₁.progress ⊂ s₂.progress :=
  e.exec.progress_ssubset

theorem deterministic (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec (e₁.tag_eq e₂) (e₁.progress_eq e₂)

end ClosedExecution
end Instantaneous

namespace Step

theorem tag_le : (s₁ ⇓ s₂) → s₁.tag ≤ s₂.tag
  | close e   => le_of_eq e.preserves_tag
  | advance a => le_of_lt a.tag_lt

theorem resolve_close : (e : s₁ ⇓ s₂) → ¬s₁.Closed → Nonempty (s₁ ⇓| s₂)
  | close e  , _ => ⟨e⟩
  | advance a, h => absurd a.closed h

theorem deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.deterministic a₂
  | close e, advance a | advance a, close e => e.step_determined a |>.elim

end Step
end Execution