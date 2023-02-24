import ReactorModel.Determinism.InstExecution

namespace Execution

open State (Closed)

variable [State.Nontrivial s] [State.Nontrivial s₁]

namespace AdvanceTag

theorem closed : (s₁ ⇓- s₂) → Closed s₁
  | ⟨_, h⟩ => h

theorem not_Closed : (s₁ ⇓- s₂) → ¬(Closed s₂)
  | ⟨hg, _⟩, hc =>
    absurd (s₁.ctx.advanceTag_progress_empty $ s₁.tag_lt_nextTag hg) hc.progress_not_empty

theorem nonrepeatable (a₁ : s₁ ⇓- s₂) (a₂ : s₂ ⇓- s₃) : False :=
  absurd a₂.closed a₁.not_Closed

theorem tag_lt : (s₁ ⇓- s₂) → s₁.tag < s₂.tag
  | mk .. => by simp [Context.advanceTag_strictly_increasing]

theorem tag_ne (a : s₁ ⇓- s₂) : s₁.tag ≠ s₂.tag :=
  ne_of_lt a.tag_lt

theorem determinisic : (s ⇓- s₁) → (s ⇓- s₂) → s₁ = s₂
  | ⟨h₁, _⟩, ⟨h₂, _⟩ => by simp [Option.some_inj.mp $ h₂ ▸ h₁]

instance preserves_Nontrivial [State.Nontrivial s₁] {e : s₁ ⇓- s₂} : State.Nontrivial s₂ :=
  match e with | ⟨_, _⟩ => inferInstance

theorem rtr_eq : (s₁ ⇓- s₂) → s₁.rtr = s₂.rtr
  | ⟨_, _⟩ => rfl

end AdvanceTag

namespace ClosedExecution

theorem not_Closed (e : s₁ ⇓| s₂) : ¬(Closed s₁) := by
  simp [Closed]
  exact e.fresh ▸ State.Nontrivial.nontrivial.symm 

theorem tag_eq (e : s₁ ⇓| s₂) : s₁.tag = s₂.tag :=
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
  e.progress_def ▸ e.exec.mem_rcns_iff rcn

theorem rcns_perm (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : e₁.rcns ~ e₂.rcns := by
  simp [List.perm_ext e₁.rcns_Nodup e₂.rcns_Nodup, e₁.mem_rcns_iff, e₂.mem_rcns_iff]

theorem ctx_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.ctx = s₂.ctx :=
  e₁.exec.ctx_eq ▸ e₂.exec.ctx_eq ▸ (Context.process_perm_eq $ e₁.rcns_perm e₂)

theorem deterministic (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec $ e₁.ctx_eq e₂

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
  | close e   => le_of_eq e.tag_eq
  | advance a => le_of_lt a.tag_lt

theorem deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.determinisic a₂
  | close e, advance a | advance a, close e => e.step_determined a |>.elim

theorem seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | close e₁,   close e₂   => e₁.nonrepeatable e₂ |>.elim
  | advance a₁, advance a₂ => a₁.nonrepeatable a₂ |>.elim
  | close e,    advance a  => e.tag_eq ▸ a.tag_lt
  | advance a,  close e    => e.tag_eq ▸ a.tag_lt

instance preserves_Nontrivial [State.Nontrivial s₁] : (s₁ ⇓ s₂) → State.Nontrivial s₂
  | close e => e.preserves_Nontrivial
  | advance a => a.preserves_Nontrivial

end Step

end Execution