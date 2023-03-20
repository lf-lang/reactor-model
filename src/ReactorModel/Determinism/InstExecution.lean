import ReactorModel.Determinism.InstStep

open Classical ReactorType

namespace Execution
namespace InstExecution

open State (Closed)

theorem rcns_unprocessed : 
  (e : s₁ ⇓ᵢ* s₂) → ∀ rcn ∈ e.rcns, rcn ∉ s₁.progress := by
  intro h rcn hr
  induction h
  case refl => sorry
    -- simp [rcns] at hr
    -- have h := h.rcn_unprocessed
    -- simp [InstStep.rcn] at h
    -- simp [hr, h]
  case trans hi =>
    cases List.mem_cons.mp hr
    case inl h _ hc => 
      simp [rcns] at hc
      have h := h.rcn_unprocessed
      simp [InstStep.rcn, ←hc] at h
      sorry -- exact h
    case inr h₁ _ h => 
      specialize hi h
      exact (not_or.mp $ (mt h₁.mem_progress.mpr) hi).right

theorem rcns_nodup : (e : s₁ ⇓ᵢ* s₂) → List.Nodup e.rcns
  | refl => List.nodup_nil
  | trans h₁ h₂ => List.nodup_cons.mpr $ ⟨(mt $ h₂.rcns_unprocessed _) $ not_not.mpr h₁.self_progress, h₂.rcns_nodup⟩

theorem mem_progress :
  (e : s₁ ⇓ᵢ* s₂) → ∀ rcn, rcn ∈ s₂.progress ↔ rcn ∈ e.rcns ∨ rcn ∈ s₁.progress := by
  intro h rcn
  induction h
  case refl => sorry -- simp [InstStep.rcn, rcns, List.mem_singleton, h.mem_progress]
  case trans h₁ h₂ hi => 
    constructor <;> intro hc 
    case mp =>
      cases hi.mp hc with
      | inl h => exact .inl $ List.mem_cons_of_mem _ h
      | inr h => 
        sorry
        -- by_cases hc : rcn ∈ (h₁.rcn :: h₂.rcns)
        -- case pos => exact .inl hc
        -- case neg => exact .inr $ (h₁.mem_progress.mp h).resolve_left $ List.ne_of_not_mem_cons hc
    case mpr =>
      cases hc with
      | inl h => 
        cases (List.mem_cons ..).mp h with
        | inl h => exact hi.mpr $ .inr (h ▸ h₁.self_progress)
        | inr h => exact hi.mpr $ .inl h
      | inr h => exact hi.mpr $ .inr $ h₁.monotonic_progress h

-- Corollary of `InstExecution.mem_progress`.
theorem self_progress : (e : s₁ ⇓ᵢ* s₂) → ∀ rcn ∈ e.rcns, rcn ∈ s₂.progress := 
  λ h _ hm => (h.mem_progress _).mpr $ .inl hm
  
theorem eq_context_processed_rcns_perm : 
  (e₁ : s ⇓ᵢ* s₁) → (e₂ : s ⇓ᵢ* s₂) → (s₁.progress = s₂.progress) → e₁.rcns ~ e₂.rcns := by
  intro h₁ h₂ hp
  apply (List.perm_ext h₁.rcns_nodup h₂.rcns_nodup).mpr
  intro rcn
  by_cases hc : rcn ∈ s.progress
  case pos =>
    have h₁ := (mt $ h₁.rcns_unprocessed rcn) (not_not.mpr hc)
    have h₂ := (mt $ h₂.rcns_unprocessed rcn) (not_not.mpr hc)
    exact iff_of_false h₁ h₂ 
  case neg =>
    constructor <;> intro hm
    case mp => 
      have h := h₁.self_progress _ hm
      sorry
      -- rw [State.progress, he] at h
      -- exact ((h₂.mem_progress _).mp h).resolve_right hc
    case mpr =>
      have h := h₂.self_progress _ hm
      sorry
      -- rw [State.progress, ←he] at h
      -- exact ((h₁.mem_progress _).mp h).resolve_right hc

/-
theorem rcn_list_cons : (e : s₁ ⇓ᵢ+ s₂) → ∃ hd tl, e.rcns = hd :: tl :=
  (by cases · <;> simp [rcns])

theorem rcns_singleton (e : s₁ ⇓ᵢ+ s₂) :
  (e.rcns = [rcn]) → ∃ e' : s₁ ⇓ᵢ s₂, (e'.rcn = rcn) ∧ (e = single e') := by
  intro h
  cases e
  case single e =>
    exists e
    simp [rcns] at h
    exact ⟨h, rfl⟩
  case trans hd tl => 
    have ⟨_, _, h'⟩ := tl.rcn_list_cons
    simp [rcns] at h
    simp [rcns, h.right] at h'

theorem Reactor.uniqueInputs' {rtr : Reactor} {iₚ i₁ i₂ : ID} :
  (iₚ ∈ rtr[.inp].ids) → (rtr[.rcn][i₁] = some rcn₁) → (rtr[.rcn][i₂] = some rcn₂) → (i₁ ≠ i₂) → 
  (.port .in iₚ ∈ rcn₁.deps .out) → .port .in iₚ ∉ rcn₂.deps .out := by
  sorry

theorem Reactor.out_port_out_dep_eq_parent {rtr : Reactor} {iₚ iᵣ : ID} :
  (iₚ ∈ rtr[.out].ids) → (rtr[.rcn][iᵣ] = some rcn) → (.port .out iₚ ∈ rcn.deps .out) → 
  (rtr[.out][iₚ]& = rtr[.rcn][iᵣ]&) := by
  sorry
-/
    




theorem preserves_tag : (s₁ ⇓ᵢ* s₂) → s₁.tag = s₂.tag
  | refl => rfl
  | trans e e' => e.preserves_tag.trans e'.preserves_tag

theorem rcns_trans_eq_cons (e₁ : s ⇓ᵢ s₁) (e₂ : s₁ ⇓ᵢ* s₂) : 
    (trans e₁ e₂).rcns = e₁.rcn.id :: e₂.rcns := by
  simp [rcns, InstStep.rcn]

theorem progress_eq : (e : s₁ ⇓ᵢ* s₂) → s₂.progress = s₁.progress ∪ { i | i ∈ e.rcns }
  | refl => by simp [rcns]
  | trans e e' => by 
    simp [e.progress_eq ▸ e'.progress_eq, rcns_trans_eq_cons]
    apply Set.insert_union'

theorem mem_rcns_not_mem_progress (e : s₁ ⇓ᵢ* s₂) (h : rcn ∈ e.rcns) : rcn ∉ s₁.progress := by
  induction e
  case refl => contradiction
  case trans e e' hi =>
    cases e'.rcns_trans_eq_cons e ▸ h
    case head   => exact e.rcn_unprocessed
    case tail h => exact mt e.monotonic_progress (hi h)

theorem mem_rcns_iff (e : s₁ ⇓ᵢ* s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₂.progress ∧ rcn ∉ s₁.progress) := by
  simp [e.progress_eq, s₁.mem_record'_progress_iff e.rcns rcn, or_and_right]
  exact e.mem_rcns_not_mem_progress

theorem equiv : (s₁ ⇓ᵢ* s₂) → s₁.rtr ≈ s₂.rtr
  | refl => .refl
  | trans e e' => Equivalent.trans e.equiv e'.equiv

theorem prepend_minimal (e : s₁ ⇓ᵢ* s₂) (hm : i ∈ e.rcns) (hi : e.rcns ≮[s₁.rtr] i) :
    ∃ (e' : s₁ ⇓ᵢ* s₂), e'.rcns = i :: (e.rcns.erase i) := by
  sorry

theorem head_minimal (e : s₁ ⇓ᵢ s₂) (e' : s₂ ⇓ᵢ* s₃) : (e.rcn :: e'.rcns) ≮[s₁.rtr] e.rcn := by
  by_contra hc
  simp [Minimal] at hc
  have ⟨_, hm, h⟩ := hc e.acyclic
  replace hc := mt e.monotonic_progress $ e'.mem_rcns_not_mem_progress hm
  exact absurd (e.allows_rcn.deps h) hc
  
theorem rcns_perm_deterministic 
    (e₁ : s ⇓ᵢ* s₁) (e₂ : s ⇓ᵢ* s₂) (hp : e₁.rcns ~ e₂.rcns) : s₁.rtr = s₂.rtr := by
  induction e₁
  case refl => cases e₂ <;> simp [rcns] at hp ⊢ 
  case trans s sₘ₁ s₁ e₁ e₁' hi =>
    have hm := hp.mem_iff.mp $ List.mem_cons_self _ _
    have hm' := e₁'.head_minimal e₁ |>.perm hp
    have ⟨e₂, he₂⟩ := e₂.prepend_minimal hm hm'
    cases e₂ <;> simp [rcns] at he₂
    case trans sₘ₂ e₂ e₂' =>
      have ⟨h, h'⟩ := he₂ 
      cases e₁.deterministic e₂ (by ext; exact h.symm)
      apply hi e₂'
      rw [h']
      exact List.perm_cons _ |>.mp (hp.trans $ List.perm_cons_erase hm)

protected theorem deterministic 
    (e₁ : s ⇓ᵢ* s₁) (e₂ : s ⇓ᵢ* s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress) : 
    s₁ = s₂ := by
  ext1 <;> try assumption
  have hp := eq_context_processed_rcns_perm e₁ e₂ hp
  exact rcns_perm_deterministic e₁ e₂ hp

end InstExecution
end Execution