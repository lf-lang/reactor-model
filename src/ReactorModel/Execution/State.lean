import ReactorModel.Execution.Reactor

noncomputable section
open Classical ReactorType Practical

namespace Execution

@[ext]
structure State (α) [Practical α] where
  rtr : α 
  tag : Time.Tag
  progress : Set ID

variable [Practical α]

namespace State

class Nontrivial (s : State α) : Prop where
  nontrivial : s.rtr[.rcn].Nonempty

theorem Nontrivial.equiv {s₁ s₂ : State α} (e : s₁.rtr ≈ s₂.rtr) [n : Nontrivial s₁] : 
    Nontrivial s₂ :=
  ⟨Equivalent.obj?_rcn_eq e ▸ n.nontrivial⟩ 

def Closed (s : State α) : Prop := 
  s.progress = s.rtr[.rcn].ids

theorem Closed.progress_Nonempty {s : State α} [Nontrivial s] (h : Closed s) : 
    s.progress.Nonempty := by
  simp_all [Closed, ←Partial.Nonempty.iff_ids_nonempty]
  exact Nontrivial.nontrivial

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
  { s with rtr := apply' s.rtr (s.output rcn) }

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
  simp [exec, output_progress_agnostic]
  rfl

def record' [DecidableEq ID] (s : State α) (rcns : List ID) : State α := 
  { s with progress := s.progress ∪ { i | i ∈ rcns } }

theorem record'_perm_eq {s : State α} (h : rcns₁ ~ rcns₂) : s.record' rcns₁ = s.record' rcns₂ := by
  simp [record', h.mem_iff]
  
theorem mem_record'_progress_iff (s : State α) (rcns : List ID) (i : ID) :
    i ∈ (s.record' rcns).progress ↔ (i ∈ s.progress ∨ i ∈ rcns) := by
  simp [record']

structure NextTag (s : State α) (next : Time.Tag) : Prop where
  mem : next ∈ scheduledTags s.rtr
  bound : s.tag < next
  least : ∀ g ∈ scheduledTags s.rtr, (s.tag < g) → (next ≤ g)    

theorem NextTag.isLeast {s : State α} (n : NextTag s g) : 
    IsLeast { g' ∈ scheduledTags s.rtr | s.tag < g' } g where
  left := ⟨n.mem, n.bound⟩
  right := by simp [lowerBounds]; exact n.least
  
theorem NextTag.deterministic {s : State α} (n₁ : NextTag s g₁) (n₂ : NextTag s g₂) : g₁ = g₂ :=
  n₁.isLeast.unique n₂.isLeast

inductive Advance : State α → State α → Prop 
  | intro : (NextTag s g) → (Cleared s.rtr c) → Advance s { rtr := c, tag := g, progress := ∅ }

namespace Advance

variable {s₁ s₂ : State α} 

theorem progress_empty : (Advance s₁ s₂) → s₂.progress = ∅
  | ⟨_, _⟩ => rfl

instance preserves_nontrivial [Nontrivial s₁] : (Advance s₁ s₂) → Nontrivial s₂
  | ⟨_, c⟩ => Nontrivial.equiv c.equiv

theorem deterministic : (Advance s s₁) → (Advance s s₂) → s₁ = s₂
  | ⟨n₁, c₁⟩, ⟨n₂, c₂⟩ => by ext1 <;> simp [n₁.deterministic n₂, c₁.deterministic c₂]
  
theorem tag_lt : (Advance s₁ s₂) → s₁.tag < s₂.tag
  | ⟨h, _⟩ => h.bound

end Advance
end State
end Execution 