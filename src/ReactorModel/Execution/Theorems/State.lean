import ReactorModel.Execution.State
import ReactorModel.Execution.Theorems.Dependency
import ReactorModel.Execution.Theorems.Reactor

open Classical Reactor

namespace Execution.State

variable [Indexable α] {s s₁ s₂ : State α}

theorem input_congr (hr : s₁.rtr = s₂.rtr := by rfl) (ht : s₁.tag = s₂.tag := by rfl) : 
    s₁.input i = s₂.input i := by
  simp [input, input.restriction, hr, ht]

theorem output_congr (hr : s₁.rtr = s₂.rtr := by rfl) (ht : s₁.tag = s₂.tag := by rfl) : 
    s₁.output i = s₂.output i := by
  simp [output, input_congr hr ht, hr]

theorem record_preserves_rtr (s : State α) (rcn : ID) : (s.record rcn).rtr = s.rtr := 
  rfl

theorem record_preserves_tag (s : State α) (rcn : ID) : (s.record rcn).tag = s.tag := 
  rfl

theorem record_preserves_events (s : State α) (rcn : ID) : (s.record rcn).events = s.events := 
  rfl

theorem record_progress_eq (s : State α) (rcn₁ rcn₂ : ID) : 
    (s.record rcn).progress = s.progress.insert rcn := 
  rfl

theorem record_preserves_output (s : State α) (rcn₁ rcn₂ : ID) : 
    (s.record rcn₁).output rcn₂ = s.output rcn₂ := 
  output_congr (s.record_preserves_rtr _) (s.record_preserves_tag _)

theorem record_comm {s : State α} {rcn₁ rcn₂ : ID} : 
    (s.record rcn₁).record rcn₂ = (s.record rcn₂).record rcn₁ := by
  simp [record]
  apply Set.insert_comm 

theorem schedule_preserves_rtr (s : State α) (i : ID) (t : Time) (v : Value) : 
    (s.schedule i t v).rtr = s.rtr := 
  rfl

theorem schedule_preserves_tag (s : State α) (i : ID) (t : Time) (v : Value) : 
    (s.schedule i t v).tag = s.tag := 
  rfl

theorem schedule_preserves_progress (s : State α) (i : ID) (t : Time) (v : Value) : 
    (s.schedule i t v).progress = s.progress := 
  rfl

theorem schedule_events_congr {s₁ s₂ : State α} {i : ID} {t : Time} {v : Value}
    (h : s₁.events = s₂.events) : (s₁.schedule i t v).events = (s₂.schedule i t v).events := by 
  simp [schedule, h]

theorem schedule_ne_comm {s : State α} {i₁ i₂ : ID} {t₁ t₂ : Time} {v₁ v₂ : Value} (h : i₁ ≠ i₂) :
    (s.schedule i₁ t₁ v₁).schedule i₂ t₂ v₂ = (s.schedule i₂ t₂ v₂).schedule i₁ t₁ v₁ := by
  simp [schedule]
  apply Partial.update_ne_comm _ h

theorem Allows.«def» : 
    (s.Allows i) ↔ (i ∈ s.rtr[.rcn]) ∧ (dependencies s.rtr i ⊆ s.progress) ∧ (i ∉ s.progress) where
  mp  := fun ⟨mem, deps, unprocessed⟩ => ⟨mem, deps, unprocessed⟩
  mpr := fun ⟨mem, deps, unprocessed⟩ => ⟨mem, deps, unprocessed⟩

theorem Allows.acyclic (a : s.Allows rcn) : ¬(rcn <[s.rtr] rcn) :=
  (a.unprocessed $ a.deps ·)

theorem Allows.congr {s₁ s₂ : State α}
    (hr : s₁.rtr ≈ s₂.rtr) (hp : s₁.progress = s₂.progress := by rfl) : 
    Allows s₁ i ↔ Allows s₂ i := by
  constructor <;> intro ⟨hm, hd, hu⟩ 
  all_goals
    exact {
      mem := by first | exact Equivalent.mem_iff hr |>.mp hm | exact Equivalent.mem_iff hr |>.mpr hm
      deps := equiv_eq_dependencies hr ▸ hp ▸ hd
      unprocessed := hp ▸ hu
    }

theorem Allows.iff_record_indep (hi : i₁ ≮[s.rtr]≯ i₂) : s.Allows i₂ ↔ (s.record i₁).Allows i₂ := by
  simp [record, Allows.def]
  intro _
  constructor <;> intro ⟨hd, hp⟩ 
  case mp =>
    constructor
    · exact hd.trans $ Set.subset_insert i₁ s.progress
    · exact Set.mem_insert_iff.not.mpr $ not_or.mpr ⟨hi.not_eq.symm, hp⟩ 
  case mpr =>
    constructor
    · exact fun _ d => Set.mem_insert_iff.mp (hd d) |>.resolve_left (hi.left $ · ▸ d)
    · exact not_or.mp (Set.mem_insert_iff.not.mp hp) |>.right

theorem Triggers.def {s : State α} : 
    (s.Triggers i) ↔ (∃ rcn, (s.rtr[.rcn][i] = some rcn) ∧ rcn.TriggersOn (s.input i)) where
  mp  := fun ⟨mem, triggers⟩ => ⟨_, mem, triggers⟩   
  mpr := fun ⟨_, mem, triggers⟩ => .intro mem triggers

theorem Triggers.congr {s₁ s₂ : State α}
    (hr : s₁.rtr = s₂.rtr := by rfl) (ht : s₁.tag = s₂.tag := by rfl) : 
    Triggers s₁ i ↔ Triggers s₂ i := by
  simp [Triggers.def, hr, input_congr hr ht]   

theorem Triggers.iff_record : s.Triggers i₂ ↔ (s.record i₁).Triggers i₂ :=
  Triggers.congr

theorem NextTag.isLeast {s : State α} (n : NextTag s g) : 
    IsLeast { g' ∈ s.scheduledTags | s.tag < g' } g where
  left := ⟨n.mem, n.bound⟩
  right := by simp [lowerBounds]; exact n.least
  
theorem NextTag.deterministic {s : State α} (n₁ : NextTag s g₁) (n₂ : NextTag s g₂) : g₁ = g₂ :=
  n₁.isLeast.unique n₂.isLeast

theorem Closed.progress_nonempty (n : s.Nontrivial) (h : Closed s) : s.progress.Nonempty := by
  simp_all [Closed, ←Partial.Nonempty.iff_ids_nonempty]
  exact n

theorem Nontrivial.equiv (e : s₁.rtr ≈ s₂.rtr) (n : s₁.Nontrivial) : s₂.Nontrivial := by
  simp_all [Nontrivial, Equivalent.obj?_rcn_eq e]

theorem Terminal.not_of_not_closed (h : ¬s.Closed) : ¬State.Terminal s :=
  (h ·.closed)

theorem Terminal.not_elim (t : ¬s.Terminal) : ¬s.Closed ∨ (∃ g, s.NextTag g) := by
  by_contra h
  push_neg at h
  exact t ⟨h.left, h.right⟩ 

end Execution.State

namespace Execution.State

variable [Proper α] {s : State α}

theorem target_not_mem_indep_output {cpt : Component.Valued}
    (h₂ : s.rtr[.rcn][i₂] = some rcn₂) (hi : i₁ ≮[s.rtr]≯ i₂) (hd : ⟨cpt, i⟩ ∈ rcn₂.deps .in) : 
    (s.output i₁).All₂ (¬·.Targets cpt i) := by
  apply List.all₂_iff_forall.mpr
  intro c hc
  simp [output] at hc
  split at hc <;> try contradiction
  case _ rcn₁ h₁ =>
    cases cpt <;> try cases ‹Component.Writable›   
    case phy => by_contra; contradiction
    all_goals
      intro ⟨⟩
      apply absurd hd
    case stv => 
      exact hi.no_shared_state_deps h₁ h₂ hc
    all_goals 
      exact hi.left.deps_disjoint h₁ h₂ (rcn₁.target_mem_deps hc) $ by simp [Change.Normal.target]

theorem indep_output_disjoint_targets (hi : i₁ ≮[s.rtr]≯ i₂) :
    Disjoint (s.output i₁).targets (s.output i₂).targets := by
  cases h₁ : s.rtr[.rcn][i₁] <;> cases h₂ : s.rtr[.rcn][i₂] <;> simp [output, h₁, h₂]
  case some.some rcn₁ rcn₂ => 
    simp [Set.disjoint_iff_forall_ne]
    intro _ _ ⟨_, hc₁, ht₁⟩ _ _ ⟨_, hc₂, ht₂⟩ hc hj
    cases hc; cases hj; cases ht₁; cases ht₂
    replace hc₁ := rcn₁.target_mem_deps hc₁
    replace hc₂ := rcn₂.target_mem_deps hc₂
    cases Dependency.shared_out_dep h₁ h₂ hi.not_eq hc₁ hc₂ <;> simp [hi.left, hi.right] at *
  all_goals simp [Reaction.Output.targets]

namespace Execution.State