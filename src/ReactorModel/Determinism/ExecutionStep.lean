import ReactorModel.Determinism.InstExecution

namespace Execution

open State (Closed)

variable [State.Nontrivial s] [State.Nontrivial s₁]

namespace AdvanceTag

theorem not_Closed (a : s₁ ⇓- s₂) : ¬(Closed s₂) :=
  have := a.advance.preserves_Nontrivial -- TODO: Make this work via type class inference.
  (absurd a.advance.progress_empty ·.progress_not_empty)

theorem nonrepeatable (a₁ : s₁ ⇓- s₂) (a₂ : s₂ ⇓- s₃) : False :=
  absurd a₂.closed a₁.not_Closed

theorem tag_lt (a : s₁ ⇓- s₂) : s₁.tag < s₂.tag :=
  a.advance.tag_lt

theorem tag_ne (a : s₁ ⇓- s₂) : s₁.tag ≠ s₂.tag :=
  ne_of_lt a.tag_lt

theorem determinisic (a₁ : s ⇓- s₁) (a₂ : s ⇓- s₂) : s₁ = s₂ :=
  a₁.advance.determinisic a₂.advance

instance preserves_Nontrivial [State.Nontrivial s₁] {e : s₁ ⇓- s₂} : State.Nontrivial s₂ :=
  e.advance.preserves_Nontrivial

end AdvanceTag

namespace ClosedExecution

theorem not_Closed (e : s₁ ⇓| s₂) : ¬(Closed s₁) := by
  simp [Closed]
  exact e.fresh ▸ State.Nontrivial.nontrivial.symm 

theorem preserves_tag (e : s₁ ⇓| s₂) : s₁.tag = s₂.tag :=
  e.exec.tag_eq

theorem preserves_rcns (e : s₁ ⇓| s₂) : s₁.rtr.ids .rcn = s₂.rtr.ids .rcn := by
  simp [Finset.ext_iff, Reactor.ids_mem_iff_obj?, e.exec.preserves_rcns]

theorem rcns_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.rtr.ids .rcn = s₂.rtr.ids .rcn :=
  e₁.preserves_rcns ▸ e₂.preserves_rcns
  
theorem rcns_Nodup (e : s₁ ⇓| s₂) : e.rcns.Nodup := 
  e.exec.rcns_nodup

theorem progress_def (e : s₁ ⇓| s₂) : s₂.progress = s₁.rtr.ids .rcn :=
  e.preserves_rcns ▸ e.closed

theorem mem_rcns_iff (e : s₁ ⇓| s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₁.rtr.ids .rcn ∧ rcn ∉ s₁.progress) :=
  e.progress_def ▸ e.exec.mem_rcns_iff

theorem rcns_perm (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : e₁.rcns ~ e₂.rcns := by
  simp [List.perm_ext e₁.rcns_Nodup e₂.rcns_Nodup, e₁.mem_rcns_iff, e₂.mem_rcns_iff]

theorem tag_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.tag = s₂.tag :=
  e₁.exec.tag_eq ▸ e₂.exec.tag_eq

theorem progress_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.progress = s₂.progress := by
  simp [e₁.progress_def, e₂.progress_def]

theorem deterministic (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec (e₁.tag_eq e₂) (e₁.progress_eq e₂)

theorem step_determined (e : s ⇓| s₁) (a : s ⇓- s₂) : False :=
  absurd a.closed e.not_Closed

instance preserves_Nontrivial [h : State.Nontrivial s₁] {e : s₁ ⇓| s₂} : State.Nontrivial s₂ where
  nontrivial := e.preserves_rcns ▸ h.nontrivial

theorem nonrepeatable (e₁ : s₁ ⇓| s₂) (e₂ : s₂ ⇓| s₃) : False :=
  have := e₁.preserves_Nontrivial -- TODO: Make this work via type class inference.
  absurd e₁.closed $ e₂.not_Closed

theorem progress_ssubset (e : s₁ ⇓| s₂) : s₁.progress ⊂ s₂.progress := by
  have := e.preserves_Nontrivial -- TODO: Make this work via type class inference.
  rw [e.fresh]
  exact Finset.nonempty.empty_ssubset $ e.closed.progress_not_empty

end ClosedExecution

namespace Step

theorem tag_le : (s₁ ⇓ s₂) → s₁.tag ≤ s₂.tag
  | close e   => le_of_eq e.preserves_tag
  | advance a => le_of_lt a.tag_lt

theorem deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.determinisic a₂
  | close e, advance a | advance a, close e => e.step_determined a |>.elim

theorem seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | close e₁,   close e₂   => e₁.nonrepeatable e₂ |>.elim
  | advance a₁, advance a₂ => a₁.nonrepeatable a₂ |>.elim
  | close e,    advance a  => e.preserves_tag ▸ a.tag_lt
  | advance a,  close e    => e.preserves_tag ▸ a.tag_lt

instance preserves_Nontrivial [State.Nontrivial s₁] : (s₁ ⇓ s₂) → State.Nontrivial s₂
  | close e => e.preserves_Nontrivial
  | advance a => a.preserves_Nontrivial

end Step

end Execution