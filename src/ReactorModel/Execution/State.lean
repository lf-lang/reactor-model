import ReactorModel.Execution.Reactor

noncomputable section
open Classical ReactorType Updatable Indexable

namespace Execution

@[ext]
structure State (α) [ReactorType.Indexable α] where
  rtr : α 
  tag : Time.Tag
  progress : Set ID

variable [ReactorType.Indexable α]

namespace State

class Nontrivial (s : State α) : Prop where
  nontrivial : s.rtr[.rcn].Nonempty

def Closed (s : State α) : Prop := 
  s.progress = s.rtr[.rcn].ids

theorem Closed.progress_Nonempty {s : State α} [n : Nontrivial s] (h : Closed s) : 
    s.progress.Nonempty := by
  simp_all [Closed, ←Partial.Nonempty.iff_ids_nonempty]
  exact Nontrivial.nontrivial

structure Allows (s : State α) (rcn : ID) : Prop where
  mem         : rcn ∈ s.rtr[.rcn] 
  deps        : dependencies s.rtr rcn ⊆ s.progress
  unprocessed : rcn ∉ s.progress

theorem Allows.acyclic {s : State α} (a : s.Allows rcn) : ¬(rcn <[s.rtr] rcn) :=
  fun hc => absurd (a.deps hc) a.unprocessed

def input (s : State α) (rcn : ID) : Reaction.Input where
  val cpt := s.rtr[.rcn][rcn] |>.elim ∅ (restriction · cpt)
  tag := s.tag
where 
  restriction (rcn : Reaction) (cpt : Reactor.Component.Valued) := 
    s.rtr[cpt].restrict { i | ⟨cpt, i⟩ ∈ rcn.deps .in }

def output (s : State α) (rcn : ID) : List Change := 
  s.rtr[.rcn][rcn] |>.elim [] (· $ s.input rcn)

inductive Triggers (s : State α) (i : ID) : Prop
  | intro (mem : s.rtr[.rcn][i] = some rcn) (triggers : rcn.TriggersOn (s.input i))

-- TODO: Is this being used?
theorem Triggers.progress_agnostic {s₁ s₂ : State α}
    (h : Triggers s₁ i) (hr : s₁.rtr = s₂.rtr) (ht : s₁.tag = s₂.tag) : Triggers s₂ i :=
  sorry

def exec (s : State α) (rcn : ID) : State α :=
  { s with rtr := apply' s.rtr (s.output rcn) }

def record [DecidableEq ID] (s : State α) (rcn : ID) : State α := 
  { s with progress := s.progress.insert rcn }

theorem record_preserves_rtr (s : State α) (rcn : ID) : (s.record rcn).rtr = s.rtr := 
  rfl

theorem record_preserves_tag (s : State α) (rcn : ID) : (s.record rcn).tag = s.tag := 
  rfl

theorem mem_record_progress_iff (s : State α) (rcn₁ rcn₂ : ID) : 
    rcn₁ ∈ (s.record rcn₂).progress ↔ (rcn₁ = rcn₂ ∨ rcn₁ ∈ s.progress) := by
  simp [record, Set.insert]

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

theorem NextTag.deterministic {s : State α} (n₁ : NextTag s g₁) (n₂ : NextTag s g₂) : g₁ = g₂ :=
  sorry

inductive Advance : State α → State α → Prop 
  | mk : (NextTag s next) → Advance s { s with tag := next, progress := ∅ }

variable {s₁ s₂ : State α} 

theorem Advance.progress_empty : (Advance s₁ s₂) → s₂.progress = ∅
  | mk .. => rfl

instance Advance.preserves_Nontrivial [inst : Nontrivial s₁] : (Advance s₁ s₂) → Nontrivial s₂
  | mk .. => ⟨inst.nontrivial⟩

theorem Advance.determinisic : (Advance s s₁) → (Advance s s₂) → s₁ = s₂
  | mk h₁, mk h₂ => by ext1 <;> simp [h₁.deterministic h₂]
  
theorem Advance.tag_lt : (Advance s₁ s₂) → s₁.tag < s₂.tag
  | mk h => h.bound

end State
end Execution 