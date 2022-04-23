import ReactorModel.Execution.Context
import ReactorModel.Execution.Dependency

open Port

@[ext]
structure Execution.State where
  rtr : Reactor
  ctx : Context

namespace Execution.State

structure allows (s : State) (i : ID) : Prop where
  deps : s.rtr.dependencies i ⊆ s.ctx.currentProcessedRcns
  unprocessed : i ∉ s.ctx.currentProcessedRcns

theorem allows_requires_acyclic_deps {s : State} : (s.allows rcn) → (rcn >[s.rtr]< rcn) := by
  intro ⟨hd, hu⟩
  by_contra h
  simp [Set.subset_def, Reactor.dependencies] at hd
  simp [Indep] at h
  exact absurd (hd _ h) hu

noncomputable def rcnInput (s : State) (i : ID) : Option Reaction.Input := 
  match s.rtr.con? .rcn i, s.rtr.obj? .rcn i with
  | some con, some rcn => some {
      portVals := s.rtr.obj?' .prt |>.restrict (rcn.deps .«in») |>.map (·.val),
      acts :=     s.rtr.obj?' .act |>.filterMap (· s.ctx.time) |>.restrict (rcn.deps .«in»),
      state :=    con.obj.state,
      time :=     s.ctx.time
    }
  | _, _ => none

noncomputable def rcnOutput (s : State) (i : ID) : Option (List Change) :=
  match s.rtr.obj? .rcn i, s.rcnInput i with
  | some rcn, some i => rcn i 
  | _, _ => none

-- NOTE: This is a helper lemma for the theorems below.
private theorem rcnInput_iff_obj? {s : State} : 
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

theorem rcnOutput_port_dep_only {s : State} {i : ID} (v) : 
  (s.rcnOutput i = some o) → (s.rtr.obj? .rcn i = some rcn) → (p ∉ rcn.deps .out) → .port p v ∉ o := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := aux ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  exact rcn.prtOutDepOnly x v hp
where 
  aux {j : ID} : (s.rcnOutput j = some o) → (∃ i rcn, s.rtr.obj? .rcn j = some rcn ∧ rcn i = o) := by
    intro h
    have ⟨_, hi⟩ := rcnInput_iff_rcnOutput.mpr ⟨_, h⟩
    have ⟨_, ho, hb⟩ := rcnInput_to_rcnOutput hi
    exact ⟨_, _, ho, Option.some_inj.mp $ hb.symm.trans h⟩

theorem rcnOutput_action_dep_only {s : State} {i : ID} (t v) : 
  (s.rcnOutput i = some o) → (s.rtr.obj? .rcn i = some rcn) → (a ∉ rcn.deps .out) → .action a t v ∉ o := by
  intro ho hr hp
  have ⟨x, _, hr', hb⟩ := aux ho
  simp [←hb, ←Option.some_inj.mp $ hr.symm.trans hr']
  exact rcn.actOutDepOnly x t v hp
where 
  aux {j : ID} : (s.rcnOutput j = some o) → (∃ i rcn, s.rtr.obj? .rcn j = some rcn ∧ rcn i = o) := by
    intro h
    have ⟨_, hi⟩ := rcnInput_iff_rcnOutput.mpr ⟨_, h⟩
    have ⟨_, ho, hb⟩ := rcnInput_to_rcnOutput hi
    exact ⟨_, _, ho, Option.some_inj.mp $ hb.symm.trans h⟩
  
theorem rcnOutput_congr {s₁ s₂ : State} :
  (s₁.rcnInput rcn = s₂.rcnInput rcn) → (s₁.rtr.obj? .rcn rcn = s₂.rtr.obj? .rcn rcn) → (s₁.rcnOutput rcn = s₂.rcnOutput rcn) :=
  λ h ho => by simp [rcnOutput, ←h, ho]

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