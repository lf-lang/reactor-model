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

-- Note: We have check the `if m : rcn ∈ s.rtr[.rcn]` in for each component, so that the types of 
--       `input.state`, `input.ports` and `input.acts` don't require the membership witness.
def input (s : State) (rcn : ID) : Reaction.Input := 
  { ports, acts, state, tag := s.tag }
where
  state := 
    if m : rcn ∈ s.rtr[.rcn]
    then s.rtr⟦m⟧&.rtr.state 
    else ∅ 
  ports := 
    if m : rcn ∈ s.rtr[.rcn]
    then fun k => s.rtr[.prt k].restrict { i | .port k i ∈ s.rtr⟦m⟧.deps .in }
    else fun _ => ∅ 
  acts := 
    if m : rcn ∈ s.rtr[.rcn]
    then s.rtr[.act].restrict { i | .action i ∈ s.rtr⟦m⟧.deps .in } |>.filterMap (·.lookup s.tag)
    else ∅ 

def output (s : State) (rcn : ID) : List Change := 
  if m : rcn ∈ s.rtr[.rcn] then s.rtr⟦m⟧ $ s.input rcn else []

structure Triggers (s : State) (rcn : ID) : Prop where
  mem      : rcn ∈ s.rtr[.rcn] 
  triggers : s.rtr⟦mem⟧.TriggersOn (s.input rcn)

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

/-
theorem rcnInput_iff_obj? {s : State} : 
  (∃ i, s.rcnInput rcn = some i) ↔ (∃ o, s.rtr[.rcn][rcn] = some o) := by
  constructor <;> intro ⟨_, h⟩
  case mp =>
    cases hc : s.rtr[.rcn][rcn] <;> simp [rcnInput, hc] at *
  case mpr =>
    sorry
    -- have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cpt? h
    -- simp [rcnInput, hc, h]

-- NOTE: This is a helper lemma for the theorems below.
private theorem rcnInput_iff_rcnOutput {s : State} : 
  (∃ i, s.rcnInput j = some i) ↔ (∃ o, s.rcnOutput j = some o) := by
  constructor <;> (
    intro h; simp [rcnInput, rcnOutput] at *
    cases ho : s.rtr[.rcn][j]
    case none => simp [ho] at h
    case some => sorry -- have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cpt? ho; simp [hc]
  )

theorem rcnInput_ports_def {s : State} :
  (s.rcnInput j = some ⟨p, x, y, z⟩) → (s.rtr[.rcn][j] = some rcn) → (p = fun k => s.rtr[.prt k].restrict { i | Reaction.Dependency.port k i ∈ rcn.deps .in }) := by
  intro hi ho
  sorry
  -- have ⟨c, hc, _⟩ := Reactor.obj?_to_con?_and_cpt? ho
  -- simp [rcnInput, hc, ho] at hi
  -- exact hi.left.symm

theorem rcnInput_actions_def {s : State} :
  (s.rcnInput j = some ⟨x, a, y, z⟩) → (s.rtr[.rcn][j] = some rcn) → (a = (s.rtr[.act].restrict { i | Reaction.Dependency.action i ∈ rcn.deps .in } |>.filterMap (·.lookup s.tag))) := by
  intro hi ho
  sorry
  -- have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cpt? ho
  -- simp [rcnInput, hc, ho] at hi
  -- exact hi.right.left.symm

theorem rcnInput_state_def {s : State} : 
  (s.rcnInput j = some ⟨x, y, q, z⟩) → (s.rtr[.rcn][j]& = some c) → (q = c.obj.state) := by
  intro hi hc
  sorry
  -- have ⟨_, ho, _⟩ := Reactor.con?_to_obj?_and_cpt? hc
  -- simp [rcnInput, hc, ho] at hi
  -- exact hi.right.right.left.symm

theorem rcnInput_time_def {s : State} : (s.rcnInput j = some ⟨x, y, z, t⟩) → (t = s.tag) := by
  intro hi
  simp [rcnInput] at hi
  cases hc : s.rtr[.rcn][j]&
  case none => simp [hc] at hi
  case some => sorry
    -- have ⟨_, ho, _⟩ := Reactor.con?_to_obj?_and_cpt? hc
    -- simp [rcnInput, hc, ho] at hi
    -- exact hi.right.right.right.symm
    
theorem rcnInput_to_rcnOutput {s : State} : 
  (s.rcnInput j = some i) → (∃ rcn, s.rtr[.rcn][j] = some rcn ∧ s.rcnOutput j = rcn i) := by
  intro h
  have ⟨_, ho⟩ := rcnInput_iff_obj?.mp ⟨_, h⟩
  exact ⟨_, ho, by simp [rcnOutput, ho, h]⟩

theorem rcnOutput_to_contains {s : State} :
  (s.rcnOutput rcn = some o) → (rcn ∈ s.rtr[.rcn].ids) := by
  intro h
  cases ho : s.rtr[.rcn][rcn]
  case none => simp [rcnOutput, ho] at h
  case some => sorry -- exact Reactor.contains_iff_obj?.mpr ⟨_, ho⟩

private theorem rcnOutput_to_rcn_body {s : State} {j : ID} : 
  (s.rcnOutput j = some o) → (∃ i rcn, s.rtr[.rcn][j] = some rcn ∧ rcn i = o) := by
  intro h
  have ⟨_, hi⟩ := rcnInput_iff_rcnOutput.mpr ⟨_, h⟩
  have ⟨_, ho, hb⟩ := rcnInput_to_rcnOutput hi
  exact ⟨_, _, ho, Option.some_inj.mp $ hb.symm.trans h⟩

theorem rcnOutput_port_dep_only {s : State} (v) : 
  (s.rcnOutput i = some o) → (s.rtr[.rcn][i] = some rcn) → (.port k p v ∈ o) → .port k p ∈ rcn.deps .out := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := rcnOutput_to_rcn_body ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  sorry -- exact rcn.prtOutDepOnly x v hp

theorem rcnOutput_action_dep_only {s : State}(t v) : 
  (s.rcnOutput i = some o) → (s.rtr[.rcn][i] = some rcn) → (.action a t v ∈ o) → (.action a ∈ rcn.deps .out) := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := rcnOutput_to_rcn_body ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  sorry -- exact rcn.actOutDepOnly x t v hp

theorem rcnOutput_pure {s : State} (v) : 
  (s.rcnOutput i = some o) → (s.rtr[.rcn][i] = some rcn) → (rcn.Pure) → .state j v ∉ o := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := rcnOutput_to_rcn_body ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  by_contra hc
  have hc := hp.output hc
  simp at hc
  sorry

theorem rcnOutput_state_local {s : State} (v) : 
  (s.rcnOutput i = some o) → (s.rtr[.rcn][i]& = some c) →
  (j ∉ c.obj.state.ids) → .state j v ∉ o := by
  intro h hc hs hm
  sorry
  -- have ⟨rcn, ho, _⟩ := Reactor.con?_to_obj?_and_cpt? hc
  -- simp [rcnOutput, rcnInput, hc, ho] at h
  -- rw [←h] at hm
  -- exact absurd (rcn.stateLocal hm) hs

theorem rcnOutput_congr {s₁ s₂ : State} :
  (s₁.rcnInput rcn = s₂.rcnInput rcn) → (s₁.rtr[.rcn][rcn] = s₂.rtr[.rcn][rcn]) → (s₁.rcnOutput rcn = s₂.rcnOutput rcn) :=
  (by simp [rcnOutput, ←·, ·])

theorem rcnOutput_pure_congr {s₁ s₂ : State} :
  (s₁.rcnInput i = some ⟨p, a, x₁, t⟩) → (s₂.rcnInput i = some ⟨p, a, x₂, t⟩) → 
  (s₁.rtr[.rcn][i] = some rcn) → (s₂.rtr[.rcn][i] = some rcn) → (rcn.Pure) →
  (s₁.rcnOutput i = s₂.rcnOutput i) :=
  λ hi₁ hi₂ ho₁ ho₂ hp => by simp [rcnOutput, ho₁, ho₂, hi₁, hi₂, hp.input _ x₁, hp.input _ x₂]
  
-/