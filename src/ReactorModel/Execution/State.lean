import ReactorModel.Execution.Reactor

noncomputable section
open Classical

namespace Execution

@[ext]
structure State where
  rtr : Reactor
  tag : Time.Tag
  progress : Set ID

namespace State

class Nontrivial (s : State) : Prop where
  nontrivial : s.rtr[.rcn].Nonempty

def Closed (s : State) : Prop := 
  s.progress = s.rtr[.rcn].ids

theorem Closed.progress_Nonempty [n : Nontrivial s] (h : Closed s) : s.progress.Nonempty := by
  simp_all [Closed, ←Partial.Nonempty.iff_ids_nonempty]
  exact Nontrivial.nontrivial

structure Allows (s : State) (rcn : ID) : Prop where
  mem         : rcn ∈ s.rtr[.rcn] 
  deps        : s.rtr.dependencies rcn ⊆ s.progress
  unprocessed : rcn ∉ s.progress

theorem Allows.acyclic {s : State} (a : s.Allows rcn) : ¬(rcn <[s.rtr] rcn) :=
  fun hc => absurd (a.deps hc) a.unprocessed

def input (s : State) (rcn : ID) : Reaction.Input where
  val cpt := s.rtr[.rcn][rcn] |>.elim ∅ (restriction · cpt)
  tag := s.tag
where 
  restriction (rcn : Reaction) (cpt : Reactor.Component.Valued) := 
    s.rtr[cpt].restrict { i | ⟨cpt, i⟩ ∈ rcn.deps .in }

def output (s : State) (rcn : ID) : List Change := 
  s.rtr[.rcn][rcn] |>.elim [] (· $ s.input rcn)

inductive Triggers (s : State) (i : ID) : Prop
  | intro (mem : s.rtr[.rcn][i] = some rcn) (triggers : rcn.TriggersOn (s.input i))

-- TODO: Is this being used?
theorem Triggers.progress_agnostic 
    (h : Triggers s₁ i) (hr : s₁.rtr = s₂.rtr) (ht : s₁.tag = s₂.tag) : Triggers s₂ i :=
  sorry

def exec (s : State) (rcn : ID) : State :=
  { s with rtr := s.rtr.apply' (s.output rcn) }

def record [DecidableEq ID] (s : State) (rcn : ID) : State := 
  { s with progress := s.progress.insert rcn }

theorem record_preserves_rtr (s : State) (rcn : ID) : (s.record rcn).rtr = s.rtr := 
  rfl

theorem record_preserves_tag (s : State) (rcn : ID) : (s.record rcn).tag = s.tag := 
  rfl

theorem mem_record_progress_iff (s : State) (rcn₁ rcn₂ : ID) : 
    rcn₁ ∈ (s.record rcn₂).progress ↔ (rcn₁ = rcn₂ ∨ rcn₁ ∈ s.progress) := by
  simp [record, Set.insert]

def record' [DecidableEq ID] (s : State) (rcns : List ID) : State := 
  { s with progress := s.progress ∪ { i | i ∈ rcns } }

theorem record'_perm_eq {s : State} (h : rcns₁ ~ rcns₂) : s.record' rcns₁ = s.record' rcns₂ := by
  simp [record', h.mem_iff]
  
theorem mem_record'_progress_iff (s : State) (rcns : List ID) (i : ID) :
    i ∈ (s.record' rcns).progress ↔ (i ∈ s.progress ∨ i ∈ rcns) := by
  simp [record']

structure NextTag (s : State) (next : Time.Tag) : Prop where
  mem : next ∈ s.rtr.scheduledTags
  bound : s.tag < next
  least : ∀ g ∈ s.rtr.scheduledTags, (s.tag < g) → (next ≤ g)    

theorem NextTag.deterministic (n₁ : NextTag s g₁) (n₂ : NextTag s g₂) : g₁ = g₂ :=
  sorry

inductive Advance : State → State → Prop 
  | mk : (NextTag s next) → Advance s { s with tag := next, progress := ∅ }

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