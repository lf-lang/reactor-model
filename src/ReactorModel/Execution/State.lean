import ReactorModel.Execution.Reactor

noncomputable section
open Classical ReactorType Practical

namespace List

def targets (cs : List Change) :=
  { t : Component.Valued × ID | ∃ c ∈ cs, c.Targets t.fst t.snd }

theorem mem_targets_cons (h : t ∈ tl.targets) : t ∈ (hd :: tl).targets := by
  have ⟨c, hm, _⟩ := h 
  exists c, by simp [hm]

theorem target_mem_targets {cs : List Change} (hc : c ∈ cs) (ht : c.target = some t) : 
    t ∈ cs.targets := by
  exists c, hc
  cases c <;> simp [Change.target] at *
  subst ht
  constructor

end List

namespace Execution

-- TODO?: Factor out a context again.
@[ext]
structure State (α) [Practical α] where
  rtr      : α 
  tag      : Time.Tag
  progress : Set ID
  events   : ID ⇀ Time.Tag ⇉ Value -- For each action we keep a mapping of tag to value.

variable [Practical α]

namespace State

def actions (s : State α) (g : Time.Tag) : ID ⇀ Value := 
  fun i => s.events i >>= (· g)

def schedule (a : Time.Tag ⇉ Value) (t : Time) (v : Value) : Time.Tag ⇉ Value :=
  match a.keys.filter (·.time = t) |>.max with
  | ⊥           => a.insert ⟨t, 0⟩ v
  | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

def apply (s : State α) : Change → State α 
  | .inp i v   => { s with    rtr := Updatable.update s.rtr .inp i v }
  | .out i v   => { s with    rtr := Updatable.update s.rtr .out i v }
  | .stv i v   => { s with    rtr := Updatable.update s.rtr .stv i v }
  | .act i t v => { s with events := s.events.update i (schedule · t v) }
  | .mut ..    => s -- Mutations are currently no-ops.

def apply' (s : State α) (cs : List Change) : State α :=
  cs.foldl apply s

def scheduledTags (s : State α) : Set Time.Tag := 
  { g | ∃ i a, (s.events i = some a) ∧ (g ∈ a.keys) }

scoped macro "cases_change " change:term : tactic => `(tactic| 
  cases $change:term <;> try cases ‹Change.Normal›; cases ‹Component.Valued›
)

theorem apply_equiv (s : State α) (c : Change) : (apply s c).rtr ≈ s.rtr := by
  cases_change c <;> first | exact .refl _ | apply Equivalent.symm; apply LawfulUpdatable.equiv

theorem apply_preserves_unchanged {c : Change} (s : State α) (h : ¬c.Targets cpt i) :
    (apply s c).rtr[cpt][i] = s.rtr[cpt][i] := by
  cases_change c
  all_goals first | exact .refl _ | exact LawfulUpdatable.obj?_preserved (Change.Targets.norm_not h)

variable {s : State α} in section

theorem apply_input_change (h : i ∈ s.rtr[.inp]) : (apply s $ .inp i v).rtr[.inp][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_output_change (h : i ∈ s.rtr[.out]) : (apply s $ .out i v).rtr[.out][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_state_change (h : i ∈ s.rtr[.stv]) : (apply s $ .stv i v).rtr[.stv][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_ne_target_comm (ht : c₁.target ≠ c₂.target ∨ c₁.target = none) : 
    apply (apply s c₁) c₂ = apply (apply s c₂) c₁ := by
  sorry -- by ext1?
  /-cases_change c₁ <;> cases_change c₂ <;> simp [apply, Change.target] at *
  all_goals exact LawfulUpdatable.update_ne_comm $ by simp_all
  -/  

theorem apply'_equiv (s : State α) : (cs : List Change) → (apply' s cs).rtr ≈ s.rtr 
  | .nil        => .refl _
  | .cons hd tl => Equivalent.trans (apply'_equiv (apply s hd) tl) (apply_equiv s hd)

theorem apply'_preserves_tag {cs : List Change} : (apply' s cs).tag = s.tag := by
  sorry

theorem apply'_preserves_progress {cs : List Change} : (apply' s cs).progress = s.progress := by
  sorry

theorem apply'_preserves_unchanged {cs : List Change} {cpt : Component.Valued} {i}
    (h : cs.All₂ (¬·.Targets cpt i)) : (apply' s cs).rtr[cpt][i] = s.rtr[cpt][i] := by
  induction cs generalizing s <;> try rfl
  case cons hd tl hi => 
    have ⟨hh, ht⟩ := List.all₂_cons _ _ _ |>.mp h
    exact apply_preserves_unchanged s hh ▸ hi ht 

theorem apply'_apply_ne_targets_comm (ht : ∀ {t}, c.target = some t → t ∉ cs.targets) : 
    apply (apply' s cs) c = apply' (apply s c) cs := by
  induction cs generalizing s <;> simp [apply'] at *
  case cons hd tl hi =>
    suffices h : hd.target ≠ c.target ∨ hd.target = none by 
      rw [hi $ fun _ _ h hm => ht _ _ h $ List.mem_targets_cons hm, apply_ne_target_comm h]
    by_contra hc
    push_neg at hc
    have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
    exact ht _ _ (hc.left ▸ h.symm) $ List.target_mem_targets (by simp) h.symm

theorem apply'_disjoint_targets_comm (ht : Disjoint cs₁.targets cs₂.targets) : 
    apply' (apply' s cs₁) cs₂ = apply' (apply' s cs₂) cs₁ := by
  induction cs₁ generalizing s <;> cases cs₂ <;> simp [apply'] at *
  case cons.cons hd₁ tl₁ hd₂ tl₂ hi =>
    have h₁ : Disjoint (List.targets tl₁) (List.targets (hd₂ :: tl₂)) := by
      simp [Set.disjoint_iff_forall_ne]
      intro _ _ hm₁ _ _ hm₂ h₁ h₂
      subst h₁ h₂    
      exact Set.disjoint_left.mp ht (List.mem_targets_cons hm₁) hm₂
    have h₂ : hd₁.target ≠ hd₂.target ∨ hd₁.target = none := by
      by_contra hc
      push_neg at hc
      have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
      have h₁ := (hd₁ :: tl₁).target_mem_targets (by simp) h.symm
      have h₂ := (hd₂ :: tl₂).target_mem_targets (by simp) (hc.left ▸ h.symm)
      exact Set.disjoint_left.mp ht h₁ h₂
    have h₃ : ∀ {t}, hd₁.target = some t → ¬t ∈ tl₂.targets := by
      intro _ h hm
      have h₁ := (hd₁ :: tl₁).target_mem_targets (by simp) h
      exact Set.disjoint_left.mp ht h₁ $ List.mem_targets_cons hm
    rw [hi h₁, apply_ne_target_comm h₂, ←apply', ←apply', ←apply'_apply_ne_targets_comm h₃]
    rfl

end

def Closed (s : State α) : Prop := 
  s.progress = s.rtr[.rcn].ids

structure Allows (s : State α) (rcn : ID) : Prop where
  mem         : rcn ∈ s.rtr[.rcn] 
  deps        : dependencies s.rtr rcn ⊆ s.progress
  unprocessed : rcn ∉ s.progress

namespace Allows

variable {s : State α}

theorem «def» : 
    (s.Allows i) ↔ (i ∈ s.rtr[.rcn]) ∧ (dependencies s.rtr i ⊆ s.progress) ∧ (i ∉ s.progress) where
  mp  := fun ⟨mem, deps, unprocessed⟩ => ⟨mem, deps, unprocessed⟩
  mpr := fun ⟨mem, deps, unprocessed⟩ => ⟨mem, deps, unprocessed⟩

theorem acyclic (a : s.Allows rcn) : ¬(rcn <[s.rtr] rcn) :=
  (a.unprocessed $ a.deps ·)

theorem not_elim (a : ¬s.Allows rcn) : 
    (rcn ∉ s.rtr[.rcn]) ∨ (∃ i, i ∈ dependencies s.rtr rcn ∧ i ∉ s.progress) ∨ (rcn ∈ s.progress) 
    := by
  by_contra h
  push_neg at h
  exact a { mem := h.left, deps := h.right.left, unprocessed := h.right.right }

end Allows

def input (s : State α) (rcn : ID) : Reaction.Input where
  val cpt := s.rtr[.rcn][rcn] |>.elim ∅ (restriction · cpt)
  tag := s.tag
where 
  restriction (rcn : Reaction) (cpt : Component.Valued) := 
    s.rtr[cpt].restrict { i | ⟨cpt, i⟩ ∈ rcn.deps .in }

theorem input_progress_agnostic {s₁ s₂ : State α}
    (hr : s₁.rtr = s₂.rtr := by rfl) (ht : s₁.tag = s₂.tag := by rfl) : 
    s₁.input i = s₂.input i := by
  simp [input, input.restriction, hr, ht]

def output (s : State α) (rcn : ID) : List Change := 
  s.rtr[.rcn][rcn] |>.elim [] (· $ s.input rcn)

theorem output_progress_agnostic {s₁ s₂ : State α}
    (hr : s₁.rtr = s₂.rtr := by rfl) (ht : s₁.tag = s₂.tag := by rfl) : 
    s₁.output i = s₂.output i := by
  simp [output, input_progress_agnostic hr ht, hr]

inductive Triggers (s : State α) (i : ID) : Prop
  | intro (mem : s.rtr[.rcn][i] = some rcn) (triggers : rcn.TriggersOn (s.input i))

theorem Triggers.def {s : State α} : 
    (s.Triggers i) ↔ (∃ rcn, (s.rtr[.rcn][i] = some rcn) ∧ rcn.TriggersOn (s.input i)) where
  mp  := fun ⟨mem, triggers⟩ => ⟨_, mem, triggers⟩   
  mpr := fun ⟨_, mem, triggers⟩ => .intro mem triggers

theorem Triggers.progress_agnostic {s₁ s₂ : State α}
    (hr : s₁.rtr = s₂.rtr := by rfl) (ht : s₁.tag = s₂.tag := by rfl) : 
    Triggers s₁ i ↔ Triggers s₂ i := by
  simp [Triggers.def, hr, input_progress_agnostic hr ht]    

def exec (s : State α) (rcn : ID) : State α :=
  s.apply' (s.output rcn)

def record [DecidableEq ID] (s : State α) (rcn : ID) : State α := 
  { s with progress := s.progress.insert rcn }

theorem record_comm {s : State α} {rcn₁ rcn₂ : ID} : 
    (s.record rcn₁).record rcn₂ = (s.record rcn₂).record rcn₁ := by
  simp [record]
  apply Set.insert_comm 

theorem record_preserves_rtr (s : State α) (rcn : ID) : (s.record rcn).rtr = s.rtr := 
  rfl

theorem record_preserves_tag (s : State α) (rcn : ID) : (s.record rcn).tag = s.tag := 
  rfl

theorem mem_record_progress_iff (s : State α) (rcn₁ rcn₂ : ID) : 
    rcn₁ ∈ (s.record rcn₂).progress ↔ (rcn₁ = rcn₂ ∨ rcn₁ ∈ s.progress) := by
  simp [record, Set.insert]

theorem record_exec_comm {s : State α} {rcn₁ rcn₂ : ID} : 
    (s.record rcn₁).exec rcn₂ = (s.exec rcn₂).record rcn₁ := by
  sorry
  /-simp [exec, output_progress_agnostic]
  rfl
  -/

def record' [DecidableEq ID] (s : State α) (rcns : List ID) : State α := 
  { s with progress := s.progress ∪ { i | i ∈ rcns } }

theorem record'_perm_eq {s : State α} (h : rcns₁ ~ rcns₂) : s.record' rcns₁ = s.record' rcns₂ := by
  simp [record', h.mem_iff]
  
theorem mem_record'_progress_iff (s : State α) (rcns : List ID) (i : ID) :
    i ∈ (s.record' rcns).progress ↔ (i ∈ s.progress ∨ i ∈ rcns) := by
  simp [record']

structure NextTag (s : State α) (next : Time.Tag) : Prop where
  mem   : next ∈ s.scheduledTags
  bound : s.tag < next
  least : ∀ g ∈ s.scheduledTags, (s.tag < g) → (next ≤ g)    

theorem NextTag.isLeast {s : State α} (n : NextTag s g) : 
    IsLeast { g' ∈ s.scheduledTags | s.tag < g' } g where
  left := ⟨n.mem, n.bound⟩
  right := by simp [lowerBounds]; exact n.least
  
theorem NextTag.deterministic {s : State α} (n₁ : NextTag s g₁) (n₂ : NextTag s g₂) : g₁ = g₂ :=
  n₁.isLeast.unique n₂.isLeast

end State
end Execution 