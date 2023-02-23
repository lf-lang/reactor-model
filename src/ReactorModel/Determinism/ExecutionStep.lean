import ReactorModel.Determinism.InstExecution

namespace Execution

open State (Closed)

variable [State.Nontrivial s] [State.Nontrivial s₁]

theorem AdvanceTag.closed : (s₁ ⇓- s₂) → Closed s₁
  | ⟨_, h⟩ => h

theorem AdvanceTag.not_Closed : (s₁ ⇓- s₂) → ¬(Closed s₂)
  | ⟨hg, _⟩, hc =>
    absurd (s₁.ctx.advanceTag_progress_empty $ s₁.tag_lt_nextTag hg) hc.progress_not_empty

theorem AdvanceTag.nonrepeatable (a₁ : s₁ ⇓- s₂) (a₂ : s₂ ⇓- s₃) : False :=
  absurd a₂.closed a₁.not_Closed

theorem AdvanceTag.tag_lt : (s₁ ⇓- s₂) → s₁.tag < s₂.tag
  | mk .. => by simp [Context.advanceTag_strictly_increasing]

theorem AdvanceTag.determinisic : (s ⇓- s₁) → (s ⇓- s₂) → s₁ = s₂
  | ⟨h₁, _⟩, ⟨h₂, _⟩ => by simp [Option.some_inj.mp $ h₂ ▸ h₁]

instance AdvanceTag.preserves_Nontrivial [State.Nontrivial s₁] {e : s₁ ⇓- s₂} : 
    State.Nontrivial s₂ :=
  match e with | ⟨_, _⟩ => inferInstance

theorem ClosedExecution.not_Closed (e : s₁ ⇓| s₂) : ¬(Closed s₁) := 
  State.Open.not_Closed e.open

theorem ClosedExecution.tag_eq (e : s₁ ⇓| s₂) : s₁.tag = s₂.tag :=
  e.exec.tag_eq

theorem ClosedExecution.preserves_rcns (e : s₁ ⇓| s₂) : s₁.rtr.ids .rcn = s₂.rtr.ids .rcn := by
  simp [Finset.ext_iff, Reactor.ids_mem_iff_obj?, e.exec.preserves_rcns]

theorem ClosedExecution.rcns_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.rtr.ids .rcn = s₂.rtr.ids .rcn :=
  e₁.preserves_rcns ▸ e₂.preserves_rcns
  
theorem ClosedExecution.rcns_Nodup (e : s₁ ⇓| s₂) : e.rcns.Nodup := 
  e.exec.rcns_nodup

theorem ClosedExecution.progress_def (e : s₁ ⇓| s₂) : s₂.progress = s₁.rtr.ids .rcn :=
  e.preserves_rcns ▸ e.closed

theorem ClosedExecution.mem_rcns_iff (e : s₁ ⇓| s₂) (rcn : ID) : 
    rcn ∈ e.rcns ↔ (rcn ∈ s₁.rtr.ids .rcn ∧ rcn ∉ s₁.progress) :=
  e.progress_def ▸ e.exec.mem_rcns_iff rcn

theorem ClosedExecution.rcns_perm (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : e₁.rcns ~ e₂.rcns := by
  simp [List.perm_ext e₁.rcns_Nodup e₂.rcns_Nodup, e₁.mem_rcns_iff, e₂.mem_rcns_iff]

theorem ClosedExecution.ctx_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁.ctx = s₂.ctx :=
  e₁.exec.ctx_eq ▸ e₂.exec.ctx_eq ▸ (Context.process_perm_eq $ e₁.rcns_perm e₂)

theorem ClosedExecution.deterministic (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec $ e₁.ctx_eq e₂

theorem ClosedExecution.step_determined (e : s ⇓| s₁) (a : s ⇓- s₂) : False :=
  absurd a.closed e.not_Closed

instance ClosedExecution.preserves_Nontrivial [h : State.Nontrivial s₁] {e : s₁ ⇓| s₂} : 
    State.Nontrivial s₂ where
  nontrivial := e.preserves_rcns ▸ h.nontrivial

theorem ClosedExecution.nonrepeatable (e₁ : s₁ ⇓| s₂) (e₂ : s₂ ⇓| s₃) : False :=
  have := e₁.preserves_Nontrivial -- TODO: Make this work via type class inference.
  absurd e₁.closed $ e₂.not_Closed

theorem ClosedExecution.progress_ssubset (e : s₁ ⇓| s₂) : s₁.progress ⊂ s₂.progress := by
  have := e.preserves_Nontrivial -- TODO: Make this work via type class inference.
  rw [e.open]
  exact Finset.nonempty.empty_ssubset $ e.closed.progress_not_empty

instance Step.preserves_Nontrivial [State.Nontrivial s₁] {e : s₁ ⇓ s₂} : State.Nontrivial s₂ :=
  match e with 
  | close e => e.preserves_Nontrivial
  | advance a => a.preserves_Nontrivial

theorem Step.tag_le : (s₁ ⇓ s₂) → s₁.tag ≤ s₂.tag
  | close e   => le_of_eq e.tag_eq
  | advance a => le_of_lt a.tag_lt

protected theorem Step.deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.determinisic a₂
  | close e, advance a | advance a, close e => e.step_determined a |>.elim

theorem Step.seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | advance a₁, advance a₂ => a₁.nonrepeatable a₂ |>.elim
  | close e₁,   close e₂   => e₁.nonrepeatable e₂ |>.elim
  | advance a,  close e    => e.tag_eq ▸ a.tag_lt
  | close e,    advance a  => e.tag_eq ▸ a.tag_lt

end Execution