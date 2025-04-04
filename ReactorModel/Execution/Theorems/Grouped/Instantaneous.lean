import ReactorModel.Execution.Theorems.Step.Skip
import ReactorModel.Execution.Theorems.Step.Exec
import ReactorModel.Execution.Theorems.Step.Time

open Classical List Reactor
open scoped Finset

namespace Execution.Instantaneous

inductive Step [Hierarchical α] (s₁ s₂ : State α)
  | skip (s : s₁ ↓ₛ s₂)
  | exec (e : s₁ ↓ₑ s₂)

notation s₁:max " ↓ᵢ " s₂:max => Step s₁ s₂

inductive Step.TC [Hierarchical α] : State α → State α → Type
  | single : (s₁ ↓ᵢ s₂) → TC s₁ s₂
  | trans  : (s₁ ↓ᵢ s₂) → (TC s₂ s₃) → TC s₁ s₃

notation s₁:max " ↓ᵢ+ " s₂:max => Step.TC s₁ s₂

structure Closed [Hierarchical α] (s₁ s₂ : State α) where
  exec   : s₁ ↓ᵢ+ s₂
  closed : s₂.Closed

notation s₁:max " ↓ᵢ| " s₂:max => Closed s₁ s₂

namespace Step

variable [Hierarchical α] {s₁ s₂ : State α}

instance : Coe (s₁ ↓ₛ s₂) (Step s₁ s₂) where
  coe := Step.skip

instance : Coe (s₁ ↓ₑ s₂) (Step s₁ s₂) where
  coe := Step.exec

def rcn : (s₁ ↓ᵢ s₂) → α✦
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
theorem progress_monotonic {rcn : α✦} (e : s₁ ↓ᵢ s₂) (h : rcn ∈ s₁.progress) : rcn ∈ s₂.progress :=
  e.progress_eq ▸ Set.mem_insert_of_mem _ h

-- Corollary of `InstStep.progress_eq`.
theorem rcn_mem_progress (e : s₁ ↓ᵢ s₂) : e.rcn ∈ s₂.progress :=
  e.progress_eq ▸ Set.mem_insert _ _

theorem rcn_not_mem_progress (e : s₁ ↓ᵢ s₂) : e.rcn ∉ s₁.progress :=
  e.allows_rcn.unprocessed

theorem not_closed (e : s₁ ↓ᵢ s₂) : ¬s₁.Closed :=
  (· ▸ e.allows_rcn.unprocessed <| e.allows_rcn.mem)

theorem acyclic (e : s₁ ↓ᵢ s₂) : e.rcn ≮[s₁.rtr] e.rcn :=
  e.allows_rcn.acyclic

theorem progress_ssubset (e : s₁ ↓ᵢ s₂) : s₁.progress ⊂ s₂.progress := by
  simp [e.progress_eq, Set.ssubset_iff_insert]
  exists e.rcn, e.allows_rcn.unprocessed

theorem seq_wellordered (e₁ : s₁ ↓ᵢ s₂) (e₂ : s₂ ↓ᵢ s₃) : e₂.rcn ≮[s₁.rtr] e₁.rcn := by
  by_contra d
  exact e₂.allows_rcn.unprocessed <| e₁.progress_monotonic <| e₁.allows_rcn.deps d

theorem seq_rcn_ne (e₁ : s₁ ↓ᵢ s₂) (e₂ : s₂ ↓ᵢ s₃) : e₁.rcn ≠ e₂.rcn := by
  by_contra he
  exact e₂.allows_rcn.unprocessed (he ▸ e₁.rcn_mem_progress)

end Step

theorem Step.deterministic [Readable α] {s s₁ s₂ : State α}
    (e₁ : s ↓ᵢ s₁) (e₂ : s ↓ᵢ s₂) (h : e₁.rcn = e₂.rcn) : s₁ = s₂ := by
  cases e₁ <;> cases e₂ <;> simp [rcn] at h
  case skip.skip e₁ e₂ => simp [e₁.dst_eq, e₂.dst_eq, h]
  case exec.exec e₁ e₂ => simp [e₁.dst_eq, e₂.dst_eq, h, e₁.apply.deterministic (h.symm ▸ e₂.apply)]
  all_goals
    have := ‹_ ↓ₛ _›.not_triggers_rcn
    have := ‹_ ↓ₑ _›.triggers_rcn
    simp_all

namespace Step

variable [Proper α] {s₁ s₂ s₃ : State α}

-- TODO: Refactor this proof. It currently does two things (1) constructing the commuted execution
--       and (2) applying the lemmas needed to show that the commuted order produces the same state.
open State in
theorem prepend_indep' (e₁ : s₁ ↓ᵢ s₂) (e₂ : s₂ ↓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (s₃' : _) (e₁' : s₁ ↓ᵢ s₂') (e₂' : s₂' ↓ᵢ s₃'),
      (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) ∧ (s₃' = s₃) := by
  replace h : _ ≮[_]≯ _ := { not_eq := e₁.seq_rcn_ne e₂, left := h, right := e₁.seq_wellordered e₂ }
  cases e₁ <;> cases e₂
  case skip.skip e₁ e₂ =>
    have ha₁ := e₁.indep_allows_iff h.symm |>.mpr e₂.allows_rcn
    have ht₁ := e₁.triggers_iff.not.mpr e₂.not_triggers_rcn
    let s₂' := s₁.record e₂.rcn
    let f₁ : s₁ ↓ₛ s₂' := ⟨ha₁, ht₁⟩
    have ha₂ := f₁.indep_allows_iff h |>.mp e₁.allows_rcn
    have ht₂ := f₁.triggers_iff.not.mp e₁.not_triggers_rcn
    let s₃' := s₂'.record e₁.rcn
    let f₂ : s₂' ↓ₛ s₃' := ⟨ha₂, ht₂⟩
    refine ⟨_, _, .skip f₁, .skip f₂, rfl, rfl, ?_⟩
    exact Step.Skip.comm e₁ e₂ f₁ f₂ rfl rfl |>.symm
  case skip.exec e₁ e₂ =>
    have ⟨z₂, a₁⟩ := Step.Apply.RTC.construct s₁ (s₁.output e₂.rcn)
    have ha₁ := e₁.indep_allows_iff h.symm |>.mpr e₂.allows_rcn
    have ht₁ := e₁.triggers_iff.mpr e₂.triggers_rcn
    let s₂' := z₂.record e₂.rcn
    let f₁ : s₁ ↓ₑ s₂' := ⟨ha₁, ht₁, a₁⟩
    have ha₂ := f₁.indep_allows_iff h |>.mp e₁.allows_rcn
    have ht₂ := f₁.indep_triggers_iff h |>.not.mp e₁.not_triggers_rcn
    let s₃' := s₂'.record e₁.rcn
    let f₂ : s₂' ↓ₛ s₃' := ⟨ha₂, ht₂⟩
    refine ⟨_, _, .exec f₁, .skip f₂, rfl, rfl, ?_⟩
    --
    simp [e₂.dst_eq, f₂.dst_eq]
    rw [State.record_comm]
    congr!
    have a₂ := e₂.apply
    simp [e₁.dst_eq] at a₂
    exact a₁.comm_record a₂
  case exec.skip e₁ e₂ =>
    have ha₁ := e₁.indep_allows_iff h.symm |>.mpr e₂.allows_rcn
    have ht₁ := e₁.indep_triggers_iff h.symm |>.not.mpr e₂.not_triggers_rcn
    let s₂' := s₁.record e₂.rcn
    let f₁ : s₁ ↓ₛ s₂' := ⟨ha₁, ht₁⟩
    have ⟨z₃, a₂⟩ := Step.Apply.RTC.construct s₂' (s₂'.output e₁.rcn)
    have ha₂ := f₁.indep_allows_iff h |>.mp e₁.allows_rcn
    have ht₂ := f₁.triggers_iff.mp e₁.triggers_rcn
    let s₃' := z₃.record e₁.rcn
    let f₂ : s₂' ↓ₑ s₃' := ⟨ha₂, ht₂, a₂⟩
    refine ⟨_, _, .skip f₁, .exec f₂, rfl, rfl, ?_⟩
    --
    simp [e₂.dst_eq, e₁.dst_eq]
    rw [State.record_comm]
    congr!
    have a₁ := e₁.apply
    rw [s₁.record_preserves_output] at a₂
    exact a₁.comm_record a₂ |>.symm
  case exec.exec e₁ e₂ =>
    have ⟨z₂, a₁⟩ := Step.Apply.RTC.construct s₁ (s₁.output e₂.rcn)
    have ha₁ := e₁.indep_allows_iff h.symm |>.mpr e₂.allows_rcn
    have ht₁ := e₁.indep_triggers_iff h.symm |>.mpr e₂.triggers_rcn
    let s₂' := z₂.record e₂.rcn
    let f₁ : s₁ ↓ₑ s₂' := ⟨ha₁, ht₁, a₁⟩
    have ⟨z₃, a₂⟩ := Step.Apply.RTC.construct s₂' (s₂'.output e₁.rcn)
    have ha₂ := f₁.indep_allows_iff h |>.mp e₁.allows_rcn
    have ht₂ := f₁.indep_triggers_iff h |>.mp e₁.triggers_rcn
    let s₃' := z₃.record e₁.rcn
    let f₂ : s₂' ↓ₑ s₃' := ⟨ha₂, ht₂, a₂⟩
    refine ⟨_, _, .exec f₁, .exec f₂, rfl, rfl, ?_⟩
    exact Step.Exec.indep_comm e₁ e₂ f₁ f₂ rfl rfl h |>.symm

theorem prepend_indep (e₁ : s₁ ↓ᵢ s₂) (e₂ : s₂ ↓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (e₁' : s₁ ↓ᵢ s₂') (e₂' : s₂' ↓ᵢ s₃), (e₁'.rcn = e₂.rcn) ∧ (e₂'.rcn = e₁.rcn) := by
  have ⟨s₂', _, e₁', e₂', h₁, h₂, h⟩ := prepend_indep' e₁ e₂ h
  subst h
  exists s₂', e₁', e₂'

end Step

namespace Step.TC

variable [Hierarchical α] {s₁ s₂ : State α} {rcn : α✦}

def rcns {s₁ s₂ : State α} : (s₁ ↓ᵢ+ s₂) → List α✦
  | single e   => [e.rcn]
  | trans e e' => e.rcn :: e'.rcns

def length {s₁ s₂ : State α} : (s₁ ↓ᵢ+ s₂) → Nat
  | single _   => 1
  | trans _ e' => e'.length + 1

theorem length_eq_rcns_length {s₁ s₂ : State α} : (e : s₁ ↓ᵢ+ s₂) → e.length = e.rcns.length
  | single _   => rfl
  | trans _ e' => by simp [length, rcns, e'.length_eq_rcns_length]

theorem acyclic (e : s₁ ↓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ≮[s₁.rtr] rcn := by
  induction e <;> simp [rcns] at h <;> try cases ‹_ ∨ _›
  case single e           => exact h ▸ e.acyclic
  case trans.inl e _ _ h  => exact h ▸ e.acyclic
  case trans.inr e _ hi h => exact (hi h).equiv (Reactor.Equivalent.symm e.equiv)

theorem progress_not_mem_rcns (e : s₁ ↓ᵢ+ s₂) (h : rcn ∈ s₁.progress) : rcn ∉ e.rcns := by
  induction e <;> simp [rcns]
  case' trans e e' hi => simp [hi <| e.progress_monotonic h]
  all_goals exact (Step.rcn_not_mem_progress ‹_› <| · ▸ h)

theorem progress_eq (e : s₁ ↓ᵢ+ s₂) : s₂.progress = s₁.progress ∪ e.rcns := by
  induction e <;> simp [rcns]
  case single e     => exact e.progress_eq
  case trans e _ hi => simp [hi, e.progress_eq]; apply Set.insert_union'

-- Corollary of `InstExecution.progress_eq`.
theorem rcns_mem_progress (e : s₁ ↓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ∈ s₂.progress :=
  e.progress_eq ▸ Set.mem_union_right _ h

theorem rcns_ne_nil {s₁ s₂ : State α} : (e : s₁ ↓ᵢ+ s₂) → e.rcns ≠ []
  | single _ | trans .. => by simp [rcns]

theorem rcns_cons {s₁ s₂ : State α} : (e : s₁ ↓ᵢ+ s₂) → ∃ hd tl, e.rcns = hd :: tl
  | single _ | trans .. => by simp [rcns]

theorem rcns_nodup {s₁ s₂ : State α} : (e : s₁ ↓ᵢ+ s₂) → e.rcns.Nodup
  | single _   => List.nodup_singleton _
  | trans e e' => List.nodup_cons.mpr ⟨e'.progress_not_mem_rcns e.rcn_mem_progress, e'.rcns_nodup⟩

theorem progress_eq_rcns_perm
    (e₁ : s ↓ᵢ+ s₁) (e₂ : s ↓ᵢ+ s₂) (hp : s₁.progress = s₂.progress) : e₁.rcns ~ e₂.rcns := by
  apply List.perm_ext_iff_of_nodup e₁.rcns_nodup e₂.rcns_nodup |>.mpr
  intro rcn
  by_cases hc : rcn ∈ s.progress
  case pos => simp [e₁.progress_not_mem_rcns hc, e₂.progress_not_mem_rcns hc]
  case neg =>
    constructor <;> intro hm
    case' mp  => have h := e₂.progress_eq ▸ hp ▸ e₁.rcns_mem_progress hm
    case' mpr => have h := e₁.progress_eq ▸ hp.symm ▸ e₂.rcns_mem_progress hm
    all_goals exact (Set.mem_union ..).mp h |>.resolve_left hc

theorem preserves_tag {s₁ s₂ : State α} : (s₁ ↓ᵢ+ s₂) → s₁.tag = s₂.tag
  | single e   => e.preserves_tag
  | trans e e' => e.preserves_tag.trans e'.preserves_tag

theorem rcns_trans_eq_cons (e₁ : s ↓ᵢ s₁) (e₂ : s₁ ↓ᵢ+ s₂) :
    (trans e₁ e₂).rcns = e₁.rcn :: e₂.rcns := by
  simp [rcns, Step.rcn]

theorem mem_rcns_not_mem_progress (e : s₁ ↓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ∉ s₁.progress := by
  induction e
  case single e =>
    simp [rcns] at h
    exact h ▸ e.rcn_not_mem_progress
  case trans e e' hi =>
    cases e'.rcns_trans_eq_cons e ▸ h
    case head   => exact e.rcn_not_mem_progress
    case tail h => exact mt e.progress_monotonic (hi h)

theorem mem_rcns_iff (e : s₁ ↓ᵢ+ s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₂.progress ∧ rcn ∉ s₁.progress) := by
  simp [e.progress_eq, or_and_right]
  exact e.mem_rcns_not_mem_progress

theorem rcns_subset_rtr_rcns (e : s₁ ↓ᵢ+ s₂) (h : rcn ∈ e.rcns) : rcn ∈ s₁.rtr[.rcn] := by
  induction e <;> simp only [rcns, mem_cons] at h <;> cases h
  case single.inr         => contradiction
  case trans.inr e _ ih h => exact Equivalent.obj?_rcn_eq e.equiv ▸ ih h
  all_goals exact ‹_ = _› ▸ ‹_ ↓ᵢ _ ›.allows_rcn.mem

theorem equiv {s₁ s₂ : State α} : (s₁ ↓ᵢ+ s₂) → s₁.rtr ≈ s₂.rtr
  | single e   => e.equiv
  | trans e e' => Reactor.Equivalent.trans e.equiv e'.equiv

theorem head_minimal (e : s₁ ↓ᵢ s₂) (e' : s₂ ↓ᵢ+ s₃) : (e.rcn :: e'.rcns) ≮[s₁.rtr] e.rcn := by
  by_contra hc
  simp only [MinimalReaction, mem_cons, forall_eq_or_imp, not_and, not_forall, Classical.not_imp,
    Decidable.not_not] at hc
  have ⟨_, hm, h⟩ := hc e.acyclic
  replace hc := mt e.progress_monotonic <| e'.mem_rcns_not_mem_progress hm
  exact hc <| e.allows_rcn.deps h

theorem head_not_mem_tail (e : s₁ ↓ᵢ s₂) (e' : s₂ ↓ᵢ+ s₃) (h : i ∈ e'.rcns) : e.rcn ≠ i := by
  intro hc
  have := trans e e' |>.rcns_nodup
  have := hc.symm ▸ List.not_nodup_cons_of_mem h
  contradiction

theorem not_closed : (s₁ ↓ᵢ+ s₂) → ¬s₁.Closed
  | single e | trans e _ => e.not_closed

theorem progress_ssubset (e : s₁ ↓ᵢ+ s₂) : s₁.progress ⊂ s₂.progress := by
  induction e
  case single e     => exact e.progress_ssubset
  case trans e _ hi => exact e.progress_ssubset |>.trans hi

theorem progress_ne (e : s₁ ↓ᵢ+ s₂) : s₁.progress ≠ s₂.progress :=
  ne_of_lt e.progress_ssubset

theorem length_le_rcns_card [Reactor.Finite α] (e : s₁ ↓ᵢ+ s₂) : e.length ≤ s₁.rtr#.rcn := by
  rw [e.length_eq_rcns_length, ←toFinset_card_of_nodup e.rcns_nodup, Finite.card]
  apply Finset.card_le_card (fun _ => ?_)
  simp only [mem_toFinset, Set.Finite.mem_toFinset]
  apply rcns_subset_rtr_rcns

end Step.TC

namespace Step.TC

variable [Proper α] {s s₁ s₂ : State α}

-- The core lemma for `prepend_minimal`.
theorem cons_prepend_minimal
    (e : s₁ ↓ᵢ s₂) (e' : s₂ ↓ᵢ+ s₃) (hm : i ∈ e'.rcns) (hr : (e.rcn :: e'.rcns) ≮[s₁.rtr] i) :
    ∃ f : s₁ ↓ᵢ+ s₃, f.rcns = i :: e.rcn :: (e'.rcns.erase i) := by
  induction e' generalizing s₁ <;> simp [rcns] at *
  case single e' =>
    have ⟨_, f, f', ⟨hf₁, hf₂⟩⟩ := e.prepend_indep e' <| hm ▸ hr.cons_head
    exists trans f (single f')
    simp [hm, rcns, ←hf₁, ←hf₂]
  case trans s₁ s₂ s₄ e' e'' hi =>
    cases hm
    case inl hm =>
      simp [hm] at hr
      have ⟨_, f, f', ⟨hf₁, hf₂⟩⟩ := e.prepend_indep e' hr.cons_head
      exists trans f <| trans f' e''
      simp [hm, rcns, ←hf₁, ←hf₂]
    case inr hm =>
      have ⟨f, hf⟩ :=  hi e' hm <| hr.cons_tail.equiv e.equiv
      cases f <;> simp [rcns] at hf
      case trans f f'' =>
        have ⟨h₁, h₂⟩ := hf
        have ⟨_, f, f', ⟨hf₁, hf₂⟩⟩ := e.prepend_indep f <| h₁.symm ▸ hr |>.cons_head
        exists trans f <| trans f' f''
        have h₃ := e''.rcns.erase_cons_tail <| by
          simp only [beq_iff_eq]; exact head_not_mem_tail e' e'' hm
        simp [rcns, hf₁, h₁, hf₂, h₂, h₃]

theorem prepend_minimal (e : s₁ ↓ᵢ+ s₂) (hm : i ∈ e.rcns) (hr : e.rcns ≮[s₁.rtr] i) :
    ∃ (e' : s₁ ↓ᵢ+ s₂), e'.rcns = i :: (e.rcns.erase i) := by
  cases e <;> (simp [rcns] at *; try cases ‹_ ∨ _›)
  case single e =>
    exists single e
    simp [hm, rcns]
  case trans.inl e e' h =>
    exists trans e e'
    simp [rcns, h]
  case trans.inr e e' h =>
    have h' := e'.rcns.erase_cons_tail <| by simp only [beq_iff_eq]; exact head_not_mem_tail e e' h
    exact h' ▸ cons_prepend_minimal e e' h hr

theorem rcns_perm_deterministic (e₁ : s ↓ᵢ+ s₁) (e₂ : s ↓ᵢ+ s₂) (hp : e₁.rcns ~ e₂.rcns) :
    (s₁.rtr = s₂.rtr) ∧ (s₁.events = s₂.events) := by
  induction e₁
  case single e =>
    cases e₂ <;> simp [rcns] at hp ⊢
    case single e' => simp [e.deterministic e' hp]
    case trans e'  => exact absurd rfl (hp.right ▸ e'.rcns_ne_nil)
  case trans s sₘ₁ s₁ e₁ e₁' hi =>
    have hm := hp.mem_iff.mp <| List.mem_cons_self _ _
    have hm' := e₁'.head_minimal e₁ |>.perm hp
    have ⟨e₂, he₂⟩ := e₂.prepend_minimal hm hm'
    cases e₂ <;> simp [rcns] at he₂
    case trans sₘ₂ e₂ e₂' =>
      have ⟨h, h'⟩ := he₂
      cases e₁.deterministic e₂ h.symm
      apply hi e₂'
      rw [h']
      exact List.perm_cons _ |>.mp (hp.trans <| List.perm_cons_erase hm)
    case single =>
      exfalso
      simp [rcns] at hp
      have ⟨hd, tl, h⟩ := e₂.rcns_cons
      have ⟨_, _, h'⟩ := e₁'.rcns_cons
      simp only [h', h, reduceCtorEq, cons.injEq, false_or] at hp he₂
      simp [he₂.right.right] at hp

theorem deterministic (e₁ : s ↓ᵢ+ s₁) (e₂ : s ↓ᵢ+ s₂) (hp : s₁.progress = s₂.progress) :
    s₁ = s₂ := by
  have := e₁.preserves_tag ▸ e₂.preserves_tag
  have ⟨_, _⟩ := rcns_perm_deterministic e₁ e₂ <| progress_eq_rcns_perm e₁ e₂ hp
  ext1 <;> try assumption

end Step.TC

namespace Closed

variable [Hierarchical α] {s s₁ s₂ : State α}

abbrev rcns (e : s₁ ↓ᵢ| s₂) : List α✦ :=
  e.exec.rcns

def length (e : s₁ ↓ᵢ| s₂) : Nat :=
  e.exec.length

theorem length_le_rcns_card [Reactor.Finite α] (e : s₁ ↓ᵢ| s₂) : e.length ≤ s₁.rtr#.rcn :=
  e.exec.length_le_rcns_card

theorem not_closed (e : s₁ ↓ᵢ| s₂) : ¬s₁.Closed :=
  e.exec.not_closed

theorem nonrepeatable (e₁ : s₁ ↓ᵢ| s₂) (e₂ : s₂ ↓ᵢ| s₃) : False :=
  e₂.not_closed e₁.closed

theorem acyclic (e : s₁ ↓ᵢ| s₂) (h : rcn ∈ e.rcns) : rcn ≮[s₁.rtr] rcn :=
  e.exec.acyclic h

theorem preserves_tag (e : s₁ ↓ᵢ| s₂) : s₁.tag = s₂.tag :=
  e.exec.preserves_tag

theorem equiv (e : s₁ ↓ᵢ| s₂) : s₁.rtr ≈ s₂.rtr :=
  e.exec.equiv

theorem rcns_nodup (e : s₁ ↓ᵢ| s₂) : e.rcns.Nodup :=
  e.exec.rcns_nodup

theorem progress_def (e : s₁ ↓ᵢ| s₂) : s₂.progress = s₁.rtr[.rcn].ids :=
  Equivalent.obj?_rcn_eq e.equiv ▸ e.closed

theorem mem_rcns_iff (e : s₁ ↓ᵢ| s₂) : rcn ∈ e.rcns ↔ (rcn ∈ s₁.rtr[.rcn] ∧ rcn ∉ s₁.progress) := by
  simp [Partial.mem_def, e.progress_def ▸ e.exec.mem_rcns_iff (rcn := rcn)]

theorem rcns_perm (e₁ : s ↓ᵢ| s₁) (e₂ : s ↓ᵢ| s₂) : e₁.rcns ~ e₂.rcns := by
  simp [List.perm_ext_iff_of_nodup e₁.rcns_nodup e₂.rcns_nodup, e₁.mem_rcns_iff, e₂.mem_rcns_iff]

theorem tag_eq (e₁ : s ↓ᵢ| s₁) (e₂ : s ↓ᵢ| s₂) : s₁.tag = s₂.tag :=
  e₁.exec.preserves_tag ▸ e₂.exec.preserves_tag

theorem progress_eq (e₁ : s ↓ᵢ| s₁) (e₂ : s ↓ᵢ| s₂) : s₁.progress = s₂.progress := by
  simp [e₁.progress_def, e₂.progress_def]

theorem step_determined (e : s ↓ᵢ| s₁) (a : s ↓ₜ s₂) : False :=
  e.not_closed a.closed

theorem progress_ssubset (e : s₁ ↓ᵢ| s₂) : s₁.progress ⊂ s₂.progress :=
  e.exec.progress_ssubset

end Closed

theorem Closed.deterministic [Proper α] {s s₁ s₂ : State α}
    (e₁ : s ↓ᵢ| s₁) (e₂ : s ↓ᵢ| s₂) : s₁ = s₂ :=
  e₁.exec.deterministic e₂.exec (e₁.progress_eq e₂)

end Execution.Instantaneous
