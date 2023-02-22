import ReactorModel.Determinism.InstExecution

namespace Execution

open State (Closed)

theorem AdvanceTag.closed : (s₁ ⇓ₜ s₂) → Closed s₁
  | mk _ h _ => h

theorem AdvanceTag.not_Closed : (s₁ ⇓ₜ s₂) → ¬(Closed s₂)
  | mk hg _ _, h => by
    have h' := s₁.ctx.advanceTag_processedRcns_empty $ s₁.tag_lt_nextTag hg
    exact absurd h' h.processedRcns_not_empty

theorem AdvanceTag.nonrepeatable (a : s₁ ⇓ₜ s₂) : ¬(s₂ ⇓ₜ s₃) :=
  (absurd ·.closed a.not_Closed)

theorem AdvanceTag.tag_lt : (s₁ ⇓ₜ s₂) → s₁.ctx.tag < s₂.ctx.tag
  | mk .. => by simp [Context.advanceTag_strictly_increasing]

theorem AdvanceTag.determinisic : (s ⇓ₜ s₁) → (s ⇓ₜ s₂) → s₁ = s₂
  | mk hg₁ _ hc₁, mk hg₂ _ hc₂ => by
    simp only [hg₁, Option.some_inj] at hg₂
    simp [clearingPorts_unique hc₁ hc₂, Context.advanceTag, hg₂]  

theorem CompleteInstExecution.closed : (s₁ ⇓ᵢ| s₂) → Closed s₂
  | mk _ h => h

theorem CompleteInstExecution.not_Closed : (s₁ ⇓ᵢ| s₂) → ¬(Closed s₁)
  | mk e _ => e.not_Closed

theorem CompleteInstExecution.nonrepeatable (e : s₁ ⇓ᵢ| s₂) : ¬(s₂ ⇓ᵢ| s₃) :=
  (absurd e.closed ·.not_Closed)

theorem CompleteInstExecution.currentProcessedRcns_ssubset :
  (s₁ ⇓ᵢ| s₂) → s₁.ctx.currentProcessedRcns ⊂ s₂.ctx.currentProcessedRcns
  | mk e _ => e.currentProcessedRcns_ssubset

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
  fun ⟨e, _⟩ ⟨_, h, _⟩ => absurd h e.not_Closed

theorem Step.tag_le : (s₁ ⇓ s₂) → s₁.ctx.tag ≤ s₂.ctx.tag
  | close e   => le_of_eq e.tag_eq
  | advance a => le_of_lt a.tag_lt

protected theorem Step.deterministic : (s ⇓ s₁) → (s ⇓ s₂) → s₁ = s₂
  | close e₁, close e₂                      => e₁.deterministic e₂
  | advance a₁, advance a₂                  => a₁.determinisic a₂
  | close e, advance a | advance a, close e => absurd a e.not_AdvanceTag

theorem Step.seq_tag_lt : (s₁ ⇓ s₂) → (s₂ ⇓ s₃) → s₁.ctx.tag < s₃.ctx.tag
  | advance a₁, advance a₂ => absurd a₂ a₁.nonrepeatable 
  | close e₁,   close e₂   => absurd e₂ e₁.nonrepeatable
  | advance a,  close e    => e.tag_eq ▸ a.tag_lt
  | close e,    advance a  => e.tag_eq ▸ a.tag_lt

end Execution