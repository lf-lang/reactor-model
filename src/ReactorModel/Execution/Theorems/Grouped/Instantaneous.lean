import ReactorModel.Execution.Theorems.SkipStep
import ReactorModel.Execution.Theorems.ExecStep

open ReactorType

namespace Execution.Instantaneous

variable [Indexable α]

inductive Step (s₁ s₂ : State α)
  | skip (s : s₁ ↓ₛ s₂)
  | exec (e : s₁ ↓ₑ s₂)

notation s₁:max " ↓ᵢ " s₂:max => Step s₁ s₂

inductive Step.TC : State α → State α → Type
  | single : (s₁ ↓ᵢ s₂) → TC s₁ s₂
  | trans  : (s₁ ↓ᵢ s₂) → (TC s₂ s₃) → TC s₁ s₃

notation s₁:max " ↓ᵢ+ " s₂:max => Step.TC s₁ s₂

structure Closed (s₁ s₂ : State α) where
  exec   : s₁ ↓ᵢ+ s₂ 
  closed : s₂.Closed

notation s₁:max " ↓ᵢ| " s₂:max => Closed s₁ s₂

variable {s₁ s₂ : State α}

instance : Coe (s₁ ↓ₛ s₂) (Step s₁ s₂) where
  coe := Step.skip

instance : Coe (s₁ ↓ₑ s₂) (Step s₁ s₂) where
  coe := Step.exec

namespace Step
  
def rcn : (s₁ ↓ᵢ s₂) → ID 
  | skip e | exec e => e.rcn

theorem allows_rcn : (e : s₁ ↓ᵢ s₂) → s₁.Allows e.rcn 
  | skip e | exec e => e.allows_rcn

theorem preserves_tag : (s₁ ↓ᵢ s₂) → s₁.tag = s₂.tag 
  | skip e | exec e => e.preserves_tag

theorem equiv : (s₁ ↓ᵢ s₂) → s₁.rtr ≈ s₂.rtr
  | skip e | exec e => e.equiv

theorem progress_eq : (e : s₁ ↓ᵢ s₂) → s₂.progress = s₁.progress.insert e.rcn
  | skip e | exec e => e.progress_eq

-- Corollary of `InstStep.progress_eq`.
theorem progress_monotonic {rcn : ID} (e : s₁ ↓ᵢ s₂) (h : rcn ∈ s₁.progress) : rcn ∈ s₂.progress :=
  e.progress_eq ▸ Set.mem_insert_of_mem _ h

-- Corollary of `InstStep.progress_eq`.
theorem rcn_mem_progress (e : s₁ ↓ᵢ s₂) : e.rcn ∈ s₂.progress :=
  e.progress_eq ▸ Set.mem_insert _ _
  
theorem rcn_not_mem_progress (e : s₁ ↓ᵢ s₂) : e.rcn ∉ s₁.progress := 
  e.allows_rcn.unprocessed

theorem not_closed (e : s₁ ↓ᵢ s₂) : ¬s₁.Closed :=
  (· ▸ e.allows_rcn.unprocessed $ e.allows_rcn.mem)

theorem deterministic (e₁ : s ↓ᵢ s₁) (e₂ : s ↓ᵢ s₂) (h : e₁.rcn = e₂.rcn) : s₁ = s₂ := by
  cases e₁ <;> cases e₂ <;> simp [rcn] at h
  case skip.skip e₁ e₂ => simp [e₁.dst_eq, e₂.dst_eq, h]
  case exec.exec e₁ e₂ => simp [e₁.dst_eq, e₂.dst_eq, h, e₁.apply.deterministic (h.symm ▸ e₂.apply)]
  all_goals
    have := ‹_ ↓ₛ _›.not_triggers_rcn
    have := ‹_ ↓ₑ _›.triggers_rcn
    simp_all

theorem acyclic (e : s₁ ↓ᵢ s₂) : e.rcn ≮[s₁.rtr] e.rcn :=
  e.allows_rcn.acyclic

theorem progress_ssubset (e : s₁ ↓ᵢ s₂) : s₁.progress ⊂ s₂.progress := by
  simp [e.progress_eq, Set.ssubset_iff_insert]
  exists e.rcn, e.allows_rcn.unprocessed

theorem seq_wellordered (e₁ : s₁ ↓ᵢ s₂) (e₂ : s₂ ↓ᵢ s₃) : e₂.rcn ≮[s₁.rtr] e₁.rcn := by
  by_contra d
  exact e₂.allows_rcn.unprocessed $ e₁.progress_monotonic $ e₁.allows_rcn.deps d

theorem seq_rcn_ne (e₁ : s₁ ↓ᵢ s₂) (e₂ : s₂ ↓ᵢ s₃) : e₁.rcn ≠ e₂.rcn := by
  by_contra he
  exact e₂.allows_rcn.unprocessed (he ▸ e₁.rcn_mem_progress)

end Step

/- Step:

variable [Practical α] {s₁ s₂ s₃ : State α}

theorem prepend_indep' (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (s₃' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃'), 
      (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) ∧ (s₃' = s₃) := by
  have hi : _ ≮[_]≯ _ := { not_eq := e₁.seq_rcn_ne e₂, left := h, right := e₁.seq_wellordered e₂ }
  cases e₁ <;> cases e₂ <;> simp [rcn] at hi  
  case skip.skip ha₁ ht₁ rcn₂ ha₂ ht₂ =>
    have ha₁' := State.record_indep_allows_iff hi.symm |>.mp ha₁
    have ha₂' := State.record_indep_allows_iff hi |>.mpr ha₂
    have ht₁' := State.record_triggers_iff (i₁ := rcn₂) |>.not.mp ht₁
    have ht₂' := State.record_triggers_iff (i₂ := rcn₂) |>.not.mpr ht₂
    exact ⟨_, _, Step.skip ha₂' ht₂', Step.skip ha₁' ht₁', rfl, rfl, State.record_comm⟩
  case skip.exec ha₁ ht₁ _ ha₂ ht₂ =>
    have ha₁' := State.exec_record_indep_allows_iff hi |>.mp ha₁
    have ha₂' := State.record_indep_allows_iff hi |>.mpr ha₂
    have ht₁' := State.exec_record_indep_triggers_iff hi |>.not.mp ht₁
    have ht₂' := State.record_triggers_iff.mpr ht₂
    refine ⟨_, _, Step.exec ha₂' ht₂', Step.skip ha₁' ht₁', rfl, rfl, ?_⟩
    simp [rcn, State.record_exec_comm, State.record_comm]
  case exec.skip ha₁ ht₁ rcn₂ ha₂ ht₂ => 
    have ha₁' := State.record_indep_allows_iff hi.symm |>.mp ha₁
    have ha₂' := State.exec_record_indep_allows_iff hi.symm |>.mpr ha₂
    have ht₁' := State.record_triggers_iff (i₁ := rcn₂) |>.mp ht₁
    have ht₂' := State.exec_record_indep_triggers_iff hi.symm |>.not.mpr ht₂
    refine ⟨_, _, Step.skip ha₂' ht₂', Step.exec ha₁' ht₁', rfl, rfl, ?_⟩
    simp [rcn, State.record_exec_comm, State.record_comm]
  case exec.exec ha₁ ht₁ _ ha₂ ht₂ =>
    have ha₁' := State.exec_record_indep_allows_iff hi |>.mp ha₁
    have ha₂' := State.exec_record_indep_allows_iff hi.symm |>.mpr ha₂
    have ht₁' := State.exec_record_indep_triggers_iff hi |>.mp ht₁
    have ht₂' := State.exec_record_indep_triggers_iff hi.symm |>.mpr ht₂
    refine ⟨_, _, Step.exec ha₂' ht₂', Step.exec ha₁' ht₁', rfl, rfl, ?_⟩
    simp [rcn, State.record_exec_comm, State.record_comm, State.exec_indep_comm hi]

theorem prepend_indep (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃), (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) := by
  have ⟨s₂', _, e₁', e₂', h₁, h₂, h⟩ := prepend_indep' e₁ e₂ h
  subst h
  exists s₂', e₁', e₂'
-/

/- Step.TC:

variable [ReactorType.Practical α] {s₁ s₂ : State α} in section

theorem acyclic (e : s₁ ⇓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ≮[s₁.rtr] rcn := by
  induction e <;> simp [rcns] at h <;> try cases ‹_ ∨ _›   
  case single e           => exact h ▸ e.acyclic
  case trans.inl e _ _ h  => exact h ▸ e.acyclic
  case trans.inr e _ hi h => exact (hi h).equiv (ReactorType.Equivalent.symm e.equiv)

theorem progress_not_mem_rcns (e : s₁ ⇓ᵢ+ s₂) (h : rcn ∈ s₁.progress) : rcn ∉ e.rcns := by
  induction e <;> simp [rcns]
  case' trans e e' hi => simp [hi $ e.progress_monotonic h]
  all_goals exact (Step.rcn_not_mem_progress ‹_› $ · ▸ h)

theorem mem_progress_iff (e : s₁ ⇓ᵢ+ s₂) : 
    (rcn ∈ s₂.progress) ↔ (rcn ∈ e.rcns ∨ rcn ∈ s₁.progress) := by
  induction e <;> simp [rcns]
  case single e => exact e.mem_progress_iff
  case trans s₁ s₂ s₃ e e' hi => 
    simp [hi]
    constructor <;> intro
    all_goals repeat cases ‹_ ∨ _› <;> simp [*]
    case mp.inr h      => cases e.mem_progress_iff.mp h <;> simp [*]
    case mpr.inl.inl h => simp [e.rcn_mem_progress]
    case mpr.inr h     => simp [e.progress_monotonic h]

-- Corollary of `InstExecution.mem_progress_iff`.
theorem rcns_mem_progress (e : s₁ ⇓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ∈ s₂.progress := 
  e.mem_progress_iff.mpr $ .inl h

theorem rcns_ne_nil {s₁ s₂ : State α} : (e : s₁ ⇓ᵢ+ s₂) → e.rcns ≠ []
  | single _ | trans .. => by simp [rcns]

theorem rcns_cons {s₁ s₂ : State α} : (e : s₁ ⇓ᵢ+ s₂) → ∃ hd tl, e.rcns = hd :: tl
  | single _ | trans .. => by simp [rcns]

theorem rcns_nodup {s₁ s₂ : State α} : (e : s₁ ⇓ᵢ+ s₂) → e.rcns.Nodup
  | single _   => List.nodup_singleton _
  | trans e e' => List.nodup_cons.mpr ⟨e'.progress_not_mem_rcns e.rcn_mem_progress, e'.rcns_nodup⟩

theorem progress_eq_rcns_perm 
    (e₁ : s ⇓ᵢ+ s₁) (e₂ : s ⇓ᵢ+ s₂) (hp : s₁.progress = s₂.progress) : e₁.rcns ~ e₂.rcns := by
  apply List.perm_ext e₁.rcns_nodup e₂.rcns_nodup |>.mpr
  intro rcn
  by_cases hc : rcn ∈ s.progress
  case pos => simp [e₁.progress_not_mem_rcns hc, e₂.progress_not_mem_rcns hc]
  case neg =>
    constructor <;> intro hm
    case mp  => exact e₂.mem_progress_iff.mp (hp ▸ e₁.rcns_mem_progress hm) |>.resolve_right hc
    case mpr => exact e₁.mem_progress_iff.mp (hp ▸ e₂.rcns_mem_progress hm) |>.resolve_right hc

theorem preserves_tag {s₁ s₂ : State α} : (s₁ ⇓ᵢ+ s₂) → s₁.tag = s₂.tag
  | single e   => e.preserves_tag
  | trans e e' => e.preserves_tag.trans e'.preserves_tag

theorem rcns_trans_eq_cons (e₁ : s ⇓ᵢ s₁) (e₂ : s₁ ⇓ᵢ+ s₂) : 
    (trans e₁ e₂).rcns = e₁.rcn :: e₂.rcns := by
  simp [rcns, Step.rcn]

theorem progress_eq {s₁ s₂ : State α} : 
    (e : s₁ ⇓ᵢ+ s₂) → s₂.progress = s₁.progress ∪ { i | i ∈ e.rcns }
  | single e => by 
    simp [rcns]
    exact e.progress_eq
  | trans e e' => by 
    simp [e.progress_eq ▸ e'.progress_eq, rcns_trans_eq_cons]
    apply Set.insert_union'

theorem mem_rcns_not_mem_progress (e : s₁ ⇓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ∉ s₁.progress := by
  induction e
  case single e => 
    simp [rcns] at h
    exact h ▸ e.rcn_not_mem_progress
  case trans e e' hi =>
    cases e'.rcns_trans_eq_cons e ▸ h
    case head   => exact e.rcn_not_mem_progress
    case tail h => exact mt e.progress_monotonic (hi h)

theorem mem_rcns_iff (e : s₁ ⇓ᵢ+ s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₂.progress ∧ rcn ∉ s₁.progress) := by
  simp [e.progress_eq, s₁.mem_record'_progress_iff e.rcns rcn, or_and_right]
  exact e.mem_rcns_not_mem_progress

theorem equiv {s₁ s₂ : State α} : (s₁ ⇓ᵢ+ s₂) → s₁.rtr ≈ s₂.rtr
  | single e   => e.equiv
  | trans e e' => ReactorType.Equivalent.trans e.equiv e'.equiv

theorem head_minimal (e : s₁ ⇓ᵢ s₂) (e' : s₂ ⇓ᵢ+ s₃) : (e.rcn :: e'.rcns) ≮[s₁.rtr] e.rcn := by
  by_contra hc
  simp [Minimal] at hc
  have ⟨_, hm, h⟩ := hc e.acyclic
  replace hc := mt e.progress_monotonic $ e'.mem_rcns_not_mem_progress hm
  exact hc $ e.allows_rcn.deps h

theorem head_not_mem_tail (e : s₁ ⇓ᵢ s₂) (e' : s₂ ⇓ᵢ+ s₃) (h : i ∈ e'.rcns) : e.rcn ≠ i := by
  intro hc
  have := trans e e' |>.rcns_nodup
  have := hc.symm ▸ List.not_nodup_cons_of_mem h
  contradiction

end

variable [ReactorType.Practical α] {s₁ s₂ : State α}

-- The core lemma for `prepend_minimal`.
theorem cons_prepend_minimal 
    (e : s₁ ⇓ᵢ s₂) (e' : s₂ ⇓ᵢ+ s₃) (hm : i ∈ e'.rcns) (hr : (e.rcn :: e'.rcns) ≮[s₁.rtr] i) : 
    ∃ f : s₁ ⇓ᵢ+ s₃, f.rcns = i :: e.rcn :: (e'.rcns.erase i) := by
  induction e' generalizing s₁ <;> simp [rcns] at *
  case single e' =>
    have ⟨_, f, f', ⟨hf₁, hf₂⟩⟩ := e.prepend_indep e' $ hm ▸ hr.cons_head
    exists trans f (single f')
    simp [hm, rcns, ←hf₁, ←hf₂]
  case trans s₁ s₂ s₄ e' e'' hi =>
    cases hm
    case inl hm =>
      simp [hm] at hr
      have ⟨_, f, f', ⟨hf₁, hf₂⟩⟩ := e.prepend_indep e' hr.cons_head
      exists trans f $ trans f' e''
      simp [hm, rcns, ←hf₁, ←hf₂]
    case inr hm =>
      have ⟨f, hf⟩ :=  hi e' hm $ hr.cons_tail.equiv e.equiv
      cases f <;> simp [rcns] at hf
      case trans f f'' =>
        have ⟨h₁, h₂⟩ := hf
        have ⟨_, f, f', ⟨hf₁, hf₂⟩⟩ := e.prepend_indep f $ h₁.symm ▸ hr |>.cons_head
        exists trans f $ trans f' f''
        simp [rcns, hf₁, h₁, hf₂, h₂, e''.rcns.erase_cons_tail $ head_not_mem_tail e' e'' hm]

theorem prepend_minimal (e : s₁ ⇓ᵢ+ s₂) (hm : i ∈ e.rcns) (hr : e.rcns ≮[s₁.rtr] i) :
    ∃ (e' : s₁ ⇓ᵢ+ s₂), e'.rcns = i :: (e.rcns.erase i) := by
  cases e <;> (simp [rcns] at *; try cases ‹_ ∨ _›)
  case single e =>
    exists single e
    simp [hm, rcns]
  case trans.inl e e' h =>
    exists trans e e'
    simp [rcns, h]
  case trans.inr e e' h =>
    exact e'.rcns.erase_cons_tail (head_not_mem_tail e e' h) ▸ cons_prepend_minimal e e' h hr
        
theorem rcns_perm_deterministic 
    (e₁ : s ⇓ᵢ+ s₁) (e₂ : s ⇓ᵢ+ s₂) (hp : e₁.rcns ~ e₂.rcns) : 
    (s₁.rtr = s₂.rtr) ∧ (s₁.events = s₂.events) := by
  induction e₁
  case single e => 
    cases e₂ <;> simp [rcns] at hp ⊢
    case single e' => simp [e.deterministic e' hp]
    case trans e'  => exact absurd rfl (hp.right ▸ e'.rcns_ne_nil)
  case trans s sₘ₁ s₁ e₁ e₁' hi =>
    have hm := hp.mem_iff.mp $ List.mem_cons_self _ _
    have hm' := e₁'.head_minimal e₁ |>.perm hp
    have ⟨e₂, he₂⟩ := e₂.prepend_minimal hm hm'
    cases e₂ <;> simp [rcns] at he₂
    case trans sₘ₂ e₂ e₂' =>
      have ⟨h, h'⟩ := he₂ 
      cases e₁.deterministic e₂ h.symm
      apply hi e₂'
      rw [h']
      exact List.perm_cons _ |>.mp (hp.trans $ List.perm_cons_erase hm)
    case single =>
      exfalso
      simp [rcns] at hp
      have ⟨hd, tl, h⟩ := e₂.rcns_cons
      have ⟨_, _, h'⟩ := e₁'.rcns_cons
      simp [h, h'] at hp he₂
      have h := he₂.right.symm ▸ List.erase_cons e₁.rcn hd tl
      split at h <;> try assumption
      simp [←h] at hp

protected theorem deterministic 
    (e₁ : s ⇓ᵢ+ s₁) (e₂ : s ⇓ᵢ+ s₂) (ht : s₁.tag = s₂.tag) (hp : s₁.progress = s₂.progress): 
    s₁ = s₂ := by
  have ⟨_, _⟩ := rcns_perm_deterministic e₁ e₂ $ progress_eq_rcns_perm e₁ e₂ hp
  ext1 <;> try assumption

theorem not_closed : (s₁ ⇓ᵢ+ s₂) → ¬s₁.Closed
  | single e | trans e _ => e.not_closed

theorem progress_ssubset (e : s₁ ⇓ᵢ+ s₂) : s₁.progress ⊂ s₂.progress := by
  induction e
  case single e     => exact e.progress_ssubset
  case trans e _ hi => exact e.progress_ssubset |>.trans hi
-/

/- Closed:

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
-/

end Execution.Instantaneous
