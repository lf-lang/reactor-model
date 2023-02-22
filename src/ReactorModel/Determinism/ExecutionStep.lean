import ReactorModel.Determinism.InstExecution

namespace Execution

open State (InstComplete)

theorem AdvanceTag.instComplete : (s₁ ⇓ₜ s₂) → InstComplete s₁
  | mk _ h _ => h

theorem AdvanceTag.not_InstComplete : (s₁ ⇓ₜ s₂) → ¬(InstComplete s₂)
  | mk hg _ _, h => by
    have h' := s₁.ctx.advanceTag_processedRcns_empty $ s₁.tag_lt_nextTag hg
    exact absurd h' h.processedRcns_not_empty

theorem AdvanceTag.saturating (a₁ : s₁ ⇓ₜ s₂) (a₂ : s₂ ⇓ₜ s₃) : False :=
  absurd a₂.instComplete a₁.not_InstComplete

theorem AdvanceTag.tag_lt : (s₁ ⇓ₜ s₂) → s₁.ctx.tag < s₂.ctx.tag
  | mk .. => by simp [Context.advanceTag_strictly_increasing]

theorem AdvanceTag.determinisic : (s ⇓ₜ s₁) → (s ⇓ₜ s₂) → s₁ = s₂
  | mk hg₁ _ hc₁, mk hg₂ _ hc₂ => by
    simp only [hg₁, Option.some_inj] at hg₂
    simp [clearingPorts_unique hc₁ hc₂, Context.advanceTag, hg₂]  

theorem CompleteInstExecution.complete : (s₁ ⇓ᵢ| s₂) → InstComplete s₂
  | mk _ h => h

theorem CompleteInstExecution.not_InstComplete : (s₁ ⇓ᵢ| s₂) → ¬(InstComplete s₁)
  | mk e _ => e.not_InstComplete

theorem CompleteInstExecution.saturating (e₁ : s₁ ⇓ᵢ| s₂) (e₂ : s₂ ⇓ᵢ| s₃) : False :=
  absurd e₁.complete e₂.not_InstComplete

theorem CompleteInstExecution.currentProcessedRcns_monotonic :
  (s₁ ⇓ᵢ| s₂) → s₁.ctx.currentProcessedRcns ⊂ s₂.ctx.currentProcessedRcns
  | mk exec _ => exec.currentProcessedRcns_monotonic

theorem CompleteInstExecution.rcns_eq : (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.rtr.ids .rcn = s₂.rtr.ids .rcn
  | mk e₁ _, mk e₂ _ => by 
    simp [Finset.ext_iff, Reactor.ids_mem_iff_obj?, ←e₁.preserves_rcns, e₂.preserves_rcns]

theorem CompleteInstExecution.tag_eq : (s₁ ⇓ᵢ| s₂) → s₁.ctx.tag = s₂.ctx.tag
  | mk e _ => e.tag_eq

theorem CompleteInstExecution.convergent_ctx : 
  (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁.ctx = s₂.ctx := by
  intro hc₁ hc₂
  ext1
  apply Finmap.ext
  intro g
  have hc₁₂ := hc₁.rcns_eq hc₂
  cases hc₁ with | mk e₁ hc₁ => 
  cases hc₂ with | mk e₂ hc₂ => 
  by_cases hg : g = s.ctx.tag
  case pos => 
    have h₁ := hc₁ |> Option.some_inj.mpr
    have h₂ := hc₂ |> Option.some_inj.mpr
    rw [Context.currentProcessedRcns_def] at h₁ h₂
    simp only [←e₁.tag_eq, ←e₂.tag_eq, ←hg] at h₁ h₂
    simp only [h₁, h₂, hc₁₂]
  case neg => simp only [←e₁.preserves_ctx_past_future g hg, e₂.preserves_ctx_past_future g hg]

theorem CompleteInstExecution.deterministic : (s ⇓ᵢ| s₁) → (s ⇓ᵢ| s₂) → s₁ = s₂
  | i₁@(mk e₁ _), i₂@(mk e₂ _) => e₁.deterministic e₂ $ i₁.convergent_ctx i₂

theorem CompleteInstExecution.not_AdvanceTag : (s ⇓ᵢ| s₁) → ¬(s ⇓ₜ s₂) := 
  fun ⟨e, _⟩ ⟨_, h, _⟩ => absurd h e.not_InstComplete

theorem Step.tag_le : (s₁ ⇓ s₂) → s₁.ctx.tag ≤ s₂.ctx.tag
  | completeInst e => le_of_eq e.tag_eq
  | advanceTag a   => le_of_lt a.tag_lt

protected theorem Step.deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | completeInst e₁, completeInst e₂                            => e₁.deterministic e₂
  | advanceTag a₁, advanceTag a₂                                => a₁.determinisic a₂
  | completeInst e, advanceTag a | advanceTag a, completeInst e => absurd a e.not_AdvanceTag

theorem Step.seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.ctx.tag < s₃.ctx.tag
  | advanceTag a₁,   advanceTag a₂   => False.elim $ a₁.saturating a₂
  | completeInst e₁, completeInst e₂ => False.elim $ e₁.saturating e₂
  | advanceTag a,    completeInst e  => e.tag_eq ▸ a.tag_lt
  | completeInst e,  advanceTag a    => e.tag_eq ▸ a.tag_lt

end Execution