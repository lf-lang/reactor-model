import ReactorModel.Determinism.InstExecution

namespace Execution

open State (Closed)

theorem AdvanceTag.closed : (s₁ ⇓- s₂) → Closed s₁
  | mk _ h => h

theorem AdvanceTag.not_Closed : (s₁ ⇓- s₂) → ¬(Closed s₂)
  | mk hg _, h =>
    absurd (s₁.ctx.advanceTag_progress_empty $ s₁.tag_lt_nextTag hg) h.progress_not_empty

theorem AdvanceTag.nonrepeatable (a₁ : s₁ ⇓- s₂) (a₂ : s₂ ⇓- s₃) : False :=
  absurd a₂.closed a₁.not_Closed

theorem AdvanceTag.tag_lt : (s₁ ⇓- s₂) → s₁.tag < s₂.tag
  | mk .. => by simp [Context.advanceTag_strictly_increasing]

theorem AdvanceTag.determinisic : (s ⇓- s₁) → (s ⇓- s₂) → s₁ = s₂
  | mk hg₁ _, mk hg₂ _ => by simp [Option.some_inj.mp $ hg₂ ▸ hg₁]

theorem ClosedExecution.not_Closed (e : s₁ ⇓| s₂) : ¬(Closed s₁) := 
  e.exec.not_Closed

theorem ClosedExecution.nonrepeatable (e₁ : s₁ ⇓| s₂) (e₂ : s₂ ⇓| s₃) : False :=
  absurd e₁.closed e₂.not_Closed

theorem ClosedExecution.progress_ssubset (e : s₁ ⇓| s₂) : s₁.progress ⊂ s₂.progress :=
  e.exec.progress_ssubset

theorem ClosedExecution.rcns_eq (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : 
    s₁.rtr.ids .rcn = s₂.rtr.ids .rcn := by
  simp [Finset.ext_iff, Reactor.ids_mem_iff_obj?, ←e₁.exec.preserves_rcns, e₂.exec.preserves_rcns]

theorem ClosedExecution.tag_eq (e : s₁ ⇓| s₂) : s₁.tag = s₂.tag :=
  e.exec.tag_eq

theorem ClosedExecution.convergent_ctx : 
  (s ⇓| s₁) → (s ⇓| s₂) → s₁.ctx = s₂.ctx := by
  intro hc₁ hc₂
  ext1
  apply Finmap.ext
  intro g
  have hc₁₂ := hc₁.rcns_eq hc₂
  cases hc₁ with | mk e₁ hc₁ => 
  cases hc₂ with | mk e₂ hc₂ => 
  by_cases hg : g = s.tag
  case pos => 
    have h₁ := hc₁ |> Option.some_inj.mpr
    have h₂ := hc₂ |> Option.some_inj.mpr
    rw [Context.progress_def] at h₁ h₂
    simp only [←e₁.tag_eq, ←e₂.tag_eq, ←hg] at h₁ h₂
    simp only [h₁, h₂, hc₁₂]
  case neg => simp only [←e₁.preserves_ctx_past_future g hg, e₂.preserves_ctx_past_future g hg]

theorem ClosedExecution.deterministic (e₁ : s ⇓| s₁) (e₂ : s ⇓| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec $ e₁.convergent_ctx e₂

theorem ClosedExecution.step_determined (e : s ⇓| s₁) (a : s ⇓- s₂) : False :=
  absurd a.closed e.not_Closed

theorem Step.tag_le : (s₁ ⇓ s₂) → s₁.tag ≤ s₂.tag
  | close e   => le_of_eq e.tag_eq
  | advance a => le_of_lt a.tag_lt

protected theorem Step.deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.determinisic a₂
  | close e, advance a | advance a, close e => (e.step_determined a).elim

theorem Step.seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.tag < s₃.tag
  | advance a₁, advance a₂ => (a₁.nonrepeatable a₂).elim
  | close e₁,   close e₂   => (e₁.nonrepeatable e₂).elim
  | advance a,  close e    => e.tag_eq ▸ a.tag_lt
  | close e,    advance a  => e.tag_eq ▸ a.tag_lt

end Execution