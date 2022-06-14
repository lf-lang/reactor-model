import ReactorModel.Execution.Context
import ReactorModel.Execution.Dependency

open Port

@[ext]
structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

structure allows (s : State) (rcn : ID) : Prop where
  deps : s.rtr.dependencies rcn ⊆ s.ctx.currentProcessedRcns
  unprocessed : rcn ∉ s.ctx.currentProcessedRcns

theorem allows_requires_acyclic_deps {s : State} : (s.allows rcn) → (rcn >[s.rtr]< rcn) := by
  intro ⟨hd, hu⟩
  by_contra h
  simp [Set.subset_def, Reactor.dependencies] at hd
  simp [Indep] at h
  exact absurd (hd _ h) hu

noncomputable def rcnInput (s : State) (i : ID) : Option Reaction.Input := 
  match s.rtr.con? .rcn i, s.rtr.obj? .rcn i with
  | some con, some rcn => some {
      portVals := s.rtr.obj?' .prt |>.restrict (rcn.deps .in)  |>.map (·.val),
      acts :=     s.rtr.obj?' .act |>.filterMap (· s.ctx.time) |>.restrict (rcn.deps .in),
      state :=    con.obj.state, -- Equivalent: s.rtr.obj?' .stv |>.restrict con.obj.state.ids
      time :=     s.ctx.time
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

theorem rcnInput_portVals_def {s : State} :
  (s.rcnInput j = some ⟨p, x, y, z⟩) → (s.rtr.obj? .rcn j = some rcn) → (p = (s.rtr.obj?' .prt |>.restrict (rcn.deps .in) |>.map (·.val))) := by
  intro hi ho
  have ⟨c, hc, _⟩ := Reactor.obj?_to_con?_and_cmp? ho
  simp [rcnInput, hc, ho] at hi
  exact hi.left.symm

theorem rcnInput_actions_def {s : State} :
  (s.rcnInput j = some ⟨x, a, y, z⟩) → (s.rtr.obj? .rcn j = some rcn) → (a = (s.rtr.obj?' .act |>.filterMap (· s.ctx.time) |>.restrict (rcn.deps .«in»))) := by
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
  (s.rcnInput j = some ⟨x, y, z, t⟩) → (t = s.ctx.time) := by
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
  have hc := hp.output x _ hc
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

def nextTag (s : State) : Option Time.Tag :=
  s.rtr.scheduledTags.filter (s.ctx.time < ·) |>.min

theorem time_lt_nextTag {s : State} {g : Time.Tag} :
  (s.nextTag = g) → s.ctx.time < g := by 
  intro h
  simp only [nextTag] at h
  exact Finset.mem_of_min h |> (Finset.mem_filter _).mp |> And.right

def freshID (s : State) : Rooted ID → ID := s.ctx.freshID.func s.rtr

end Execution.State 