import ReactorModel.Execution.Dependency

open Classical

@[ext]
structure Execution.State where
  rtr : Reactor
  tag : Time.Tag
  progress : Finset ID

inductive Execution.Operation 
  | skip (rcn : ID)
  | exec (rcn : ID) (changes : List Change)

def Execution.Operation.rcn : Operation → ID
  | skip rcn | exec rcn _ => rcn

def Execution.Operation.changes : Execution.Operation → List (Identified Change)
  | .skip _ => []
  | .exec rcn cs => cs.map (⟨rcn, ·⟩)

namespace Execution.State

class Nontrivial (s : Execution.State) : Prop where
  nontrivial : (s.rtr.ids .rcn).Nonempty

def Closed (s : State) : Prop := s.progress = s.rtr.ids .rcn

theorem Closed.progress_Nonempty [Nontrivial s] : Closed s → s.progress.Nonempty := by
  simp_all [Closed, Nontrivial.nontrivial]  

/-
noncomputable abbrev advanceTag (s : State) (g : Time.Tag) : State := 
  { s with s := s.s.advanceTag g }

instance [Nontrivial s] : Nontrivial (s.advanceTag g) where
  nontrivial := by simp [Nontrivial.nontrivial]
-/

structure allows (s : State) (rcn : ID) : Prop where
  deps : s.rtr.dependencies rcn ⊆ s.progress
  unprocessed : rcn ∉ s.progress

theorem allows_requires_acyclic_deps {s : State} : (s.allows rcn) → (rcn >[s.rtr]< rcn) := by
  intro ⟨hd, hu⟩
  by_contra h
  simp [Set.subset_def, Reactor.dependencies] at hd
  simp [Indep] at h
  exact absurd (hd _ h) hu

noncomputable def rcnInput (s : State) (i : ID) : Option Reaction.Input := 
  match s.rtr.con? .rcn i, s.rtr.obj? .rcn i with
  | some con, some rcn => some {
      ports := s.rtr.obj?' .prt |>.restrict (rcn.deps .in)  |>.map (·.val),
      acts :=     s.rtr.obj?' .act |>.filterMap (· s.tag) |>.restrict (rcn.deps .in),
      state :=    con.obj.state, -- Equivalent: s.rtr.obj?' .stv |>.restrict con.obj.state.ids
      tag :=      s.tag
    }
  | _, _ => none

noncomputable def rcnOutput (s : State) (i : ID) : Option (List Change) :=
  match s.rtr.obj? .rcn i, s.rcnInput i with
    | some rcn, some i => rcn i 
    | _, _ => none
  
theorem rcnInput_iff_obj? {s : State} : 
  (∃ i, s.rcnInput rcn = some i) ↔ (∃ o, s.rtr.obj? .rcn rcn = some o) := by
  constructor <;> intro ⟨_, h⟩
  case mp =>
    cases hc : s.rtr.obj? .rcn rcn <;> simp [rcnInput, hc] at *
  case mpr =>
    have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? h
    simp [rcnInput, hc, h]

-- NOTE: This is a helper lemma for the theorems below.
private theorem rcnInput_iff_rcnOutput {s : State} : 
  (∃ i, s.rcnInput j = some i) ↔ (∃ o, s.rcnOutput j = some o) := by
  constructor <;> (
    intro h; simp [rcnInput, rcnOutput] at *
    cases ho : s.rtr.obj? .rcn j
    case none => simp [ho] at h
    case some => have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho; simp [hc]
  )

theorem rcnInput_ports_def {s : State} :
  (s.rcnInput j = some ⟨p, x, y, z⟩) → (s.rtr.obj? .rcn j = some rcn) → (p = (s.rtr.obj?' .prt |>.restrict (rcn.deps .in) |>.map (·.val))) := by
  intro hi ho
  have ⟨c, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho
  simp [rcnInput, hc, ho] at hi
  exact hi.left.symm

theorem rcnInput_actions_def {s : State} :
  (s.rcnInput j = some ⟨x, a, y, z⟩) → (s.rtr.obj? .rcn j = some rcn) → (a = (s.rtr.obj?' .act |>.filterMap (· s.tag) |>.restrict (rcn.deps .«in»))) := by
  intro hi ho
  have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho
  simp [rcnInput, hc, ho] at hi
  exact hi.right.left.symm

theorem rcnInput_state_def {s : State} : 
  (s.rcnInput j = some ⟨x, y, q, z⟩) → (s.rtr.con? .rcn j = some c) → (q = c.obj.state) := by
  intro hi hc
  have ⟨_, ho, _⟩ := Reactor.con?_to_obj?_and_cmp? hc
  simp [rcnInput, hc, ho] at hi
  exact hi.right.right.left.symm

theorem rcnInput_time_def {s : State} :
  (s.rcnInput j = some ⟨x, y, z, t⟩) → (t = s.tag) := by
  intro hi
  simp [rcnInput] at hi
  cases hc : s.rtr.con? .rcn j
  case none => simp [hc] at hi
  case some => 
    have ⟨_, ho, _⟩ := Reactor.con?_to_obj?_and_cmp? hc
    simp [rcnInput, hc, ho] at hi
    exact hi.right.right.right.symm
    
theorem rcnInput_to_rcnOutput {s : State} : 
  (s.rcnInput j = some i) → (∃ rcn, s.rtr.obj? .rcn j = some rcn ∧ s.rcnOutput j = rcn i) := by
  intro h
  have ⟨_, ho⟩ := rcnInput_iff_obj?.mp ⟨_, h⟩
  exact ⟨_, ho, by simp [rcnOutput, ho, h]⟩

theorem rcnOutput_to_contains {s : State} :
  (s.rcnOutput rcn = some o) → (s.rtr.contains .rcn rcn) := by
  intro h
  cases ho : s.rtr.obj? .rcn rcn
  case none => simp [rcnOutput, ho] at h
  case some => exact Reactor.contains_iff_obj?.mpr ⟨_, ho⟩

private theorem rcnOutput_to_rcn_body {s : State} {j : ID} : 
  (s.rcnOutput j = some o) → (∃ i rcn, s.rtr.obj? .rcn j = some rcn ∧ rcn i = o) := by
  intro h
  have ⟨_, hi⟩ := rcnInput_iff_rcnOutput.mpr ⟨_, h⟩
  have ⟨_, ho, hb⟩ := rcnInput_to_rcnOutput hi
  exact ⟨_, _, ho, Option.some_inj.mp $ hb.symm.trans h⟩

theorem rcnOutput_port_dep_only {s : State} (v) : 
  (s.rcnOutput i = some o) → (s.rtr.obj? .rcn i = some rcn) → (p ∉ rcn.deps .out) → .port p v ∉ o := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := rcnOutput_to_rcn_body ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  exact rcn.prtOutDepOnly x v hp

theorem rcnOutput_action_dep_only {s : State}(t v) : 
  (s.rcnOutput i = some o) → (s.rtr.obj? .rcn i = some rcn) → (a ∉ rcn.deps .out) → .action a t v ∉ o := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := rcnOutput_to_rcn_body ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  exact rcn.actOutDepOnly x t v hp

theorem rcnOutput_pure {s : State} (v) : 
  (s.rcnOutput i = some o) → (s.rtr.obj? .rcn i = some rcn) → (rcn.isPure) → .state j v ∉ o := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := rcnOutput_to_rcn_body ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  by_contra hc
  have hc := hp.output hc
  simp at hc

theorem rcnOutput_state_local {s : State} (v) : 
  (s.rcnOutput i = some o) → (s.rtr.con? .rcn i = some c) →
  (j ∉ c.obj.state.ids) → .state j v ∉ o := by
  intro h hc hs hm
  have ⟨rcn, ho, _⟩ := Reactor.con?_to_obj?_and_cmp? hc
  simp [rcnOutput, rcnInput, hc, ho] at h
  rw [←h] at hm
  exact absurd (rcn.stateLocal hm) hs

theorem rcnOutput_congr {s₁ s₂ : State} :
  (s₁.rcnInput rcn = s₂.rcnInput rcn) → (s₁.rtr.obj? .rcn rcn = s₂.rtr.obj? .rcn rcn) → (s₁.rcnOutput rcn = s₂.rcnOutput rcn) :=
  (by simp [rcnOutput, ←·, ·])

theorem rcnOutput_pure_congr {s₁ s₂ : State} :
  (s₁.rcnInput i = some ⟨p, a, x₁, t⟩) → (s₂.rcnInput i = some ⟨p, a, x₂, t⟩) → 
  (s₁.rtr.obj? .rcn i = some rcn) → (s₂.rtr.obj? .rcn i = some rcn) → (rcn.isPure) →
  (s₁.rcnOutput i = s₂.rcnOutput i) :=
  λ hi₁ hi₂ ho₁ ho₂ hp => by simp [rcnOutput, ho₁, ho₂, hi₁, hi₂, hp.input _ x₁, hp.input _ x₂]
  
def triggers (s : State) (r : ID) :=
  ∃ rcn i, (s.rtr.obj? .rcn r = some rcn) ∧ (s.rcnInput r = some i) ∧ (rcn.triggersOn i)

noncomputable def operation (s : State) (i : ID) : Option Operation :=
  if s.triggers i 
  then (s.rcnOutput i) >>= (some $ .exec i ·)
  else if s.rtr.contains .rcn i then some (.skip i)
  else none

theorem operation_to_contains {s : State} :
  (s.operation rcn = some o) → (s.rtr.contains .rcn rcn) := by
  intro h
  simp [operation] at h
  split at h
  all_goals sorry

theorem operation_some_to_Nontrivial (h : s.operation i = some o) : Nontrivial s := by
  have h := operation_to_contains h |> Reactor.ids_mem_iff_contains.mpr
  sorry

structure NextTag (s : State) (next : Time.Tag) : Prop where
  mem : next ∈ s.rtr.scheduledTags
  bound : s.tag < next
  least : ∀ g ∈ s.rtr.scheduledTags, (s.tag < g) → (next ≤ g)    

inductive Advance : State → State → Prop 
  | mk : (NextTag s next) → Advance s { s with tag := next }

instance Advance.preserves_Nontrivial [Nontrivial s₁] : (Advance s₁ s₂) → Nontrivial s₂
  | mk .. => sorry

theorem Advance.progress_empty (a : Advance s₁ s₂) : s₂.progress = ∅ :=
  sorry

theorem Advance.determinisic (a₁ : Advance s s₁) (a₂ : Advance s s₂) : s₁ = s₂ :=
  sorry

theorem Advance.tag_lt : (Advance s₁ s₂) → s₁.tag < s₂.tag
  | mk h => h.bound

def record [DecidableEq ID] (s : State) (rcn : ID) : State := 
  { s with progress := insert rcn s.progress }
  
theorem record_preserves_tag (s : State) (rcn : ID) : (s.record rcn).tag = s.tag := 
  rfl

theorem record_comm (s : State) (rcn₁ rcn₂ : ID) : 
    (s.record rcn₁).record rcn₂ = (s.record rcn₁).record rcn₂ := by
  sorry

theorem mem_record_progress_self (s : State) (rcn : ID) : rcn ∈ (s.record rcn).progress := by
  sorry

variable {s : State}

theorem record_progress_monotonic (rcn₁ : ID) : (rcn₁ ∈ s.progress) → rcn₁ ∈ (s.record rcn₂).progress := by
  sorry

theorem mem_record_progress (h : rcn₁ ∈ (s.record rcn₂).progress) : (rcn₁ = rcn₂ ∨ rcn₁ ∈ s.progress) := by
  sorry

theorem mem_record_progress_iff (s : State) (rcn₁ rcn₂ : ID) : 
    rcn₁ ∈ (s.record rcn₂).progress ↔ (rcn₁ = rcn₂ ∨ rcn₁ ∈ s.progress) where
  mp := mem_record_progress
  mpr
    | .inl h => h ▸ s.mem_record_progress_self rcn₁
    | .inr h => record_progress_monotonic _ h

def record' [DecidableEq ID] (s : State) : List ID → State
  | [] => s
  | hd :: tl => (s.record hd).record' tl

theorem record'_cons : (s.record i).record' l = s.record' (i :: l) := rfl

theorem record'_comm (s : State) (rcns : List ID) (rcn : ID) :
    (s.record' rcns).record rcn = (s.record rcn).record' rcns := by
  induction rcns generalizing s rcn
  case nil => rfl
  case cons hd tl hi => 
    simp [record', record_comm, hi]
    sorry

theorem record'_perm_eq (h : l₁ ~ l₂) : s.record' l₁ = s.record' l₂ := by
  induction h generalizing s
  case nil     => rfl
  case cons hi => simp [record', hi]
  case swap    => simp [record', record_comm]; sorry
  case trans   => simp_all

theorem record'_progress_monotonic (l : List ID) (h : i ∈ s.progress) : 
    i ∈ (s.record' l).progress := by
  induction l generalizing s i
  case nil => assumption
  case cons hd _ hi => exact hi $ record_progress_monotonic _ h

theorem record'_cons_progress_monotonic (h : i ∈ (s.record' tl).progress) : 
    i ∈ (s.record' $ hd :: tl).progress := by
  simp [record', ←record'_comm, record_progress_monotonic _ h]
  
theorem mem_list_to_mem_record'_progress (h : i ∈ l) : i ∈ (s.record' l).progress := by
  induction l
  case nil => contradiction
  case cons hd tl hi =>
    cases h
    case head   => exact record'_progress_monotonic tl $ s.mem_record_progress_self i
    case tail h => exact record'_cons_progress_monotonic $ hi h

theorem mem_record'_progress_to_mem_progress_or_mem_list (h : i ∈ (s.record' l).progress) :
    (i ∈ s.progress ∨ i ∈ l) := by
  induction l generalizing s i <;> simp_all [record']
  case cons hd tl hi =>
    cases hi h
    case inl h => cases mem_record_progress h <;> simp [*]
    case inr h => simp [h]

theorem mem_record'_progress_iff (s : State) (l : List ID) (i : ID) :
    i ∈ (s.record' l).progress ↔ (i ∈ s.progress ∨ i ∈ l) where
  mp := mem_record'_progress_to_mem_progress_or_mem_list
  mpr 
    | .inl h => record'_progress_monotonic l h
    | .inr h => mem_list_to_mem_record'_progress h

end Execution.State 