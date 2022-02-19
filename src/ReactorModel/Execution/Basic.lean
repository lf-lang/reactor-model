import ReactorModel.Execution.State

open Port

namespace Execution

noncomputable def schedule (act : Time.Tag ▸ Value) (t : Time) (v : Value) : Time.Tag ▸ Value :=
  match act.ids.filter (·.t = t) |>.max with
  | none => act.update ⟨t, 0⟩ v
  | some g => act.update ⟨t, g.microsteps + 1⟩ v

-- If port src and should be connected to port dst, is t the reactor where the relay reaction should be placed?
inductive isRelayReactor (σ : Reactor) (t : ID) (src dst : ID) : Prop
  | sameRtr {p : ID} :        (σ &[src]= p) → (σ &[dst]= p) → (σ &[p]= t)                   → isRelayReactor σ t src dst
  | bothNested {ns nd : ID} : (σ &[src]= ns) → (σ &[dst]= nd) → (σ &[ns]= t) → (σ &[nd]= t) → isRelayReactor σ t src dst
  | srcNested {n : ID} :      (σ &[src]= n) → (σ &[n]= t) → (σ &[dst]= t)                   → isRelayReactor σ t src dst
  | dstNested {n : ID} :      (σ &[dst]= n) → (σ &[n]= t) → (σ &[src]= t)                   → isRelayReactor σ t src dst

-- TODO: Can these be bundled as a derivative of the Update relation (e.g. called Mutation)?
-- NOTE: We're currently ignoring the reactions' children - what did we need those for again?

structure insertingRelayReaction (src dst : ID) (σ₁ σ₂ : Reactor) : Prop where
  eqCmps : ∀ cmp, (cmp ≠ Cmp.rcn) → σ₁.cmp cmp = σ₂.cmp cmp
  insert : ∃ i, (i ∉ σ₁.rcns.ids) ∧ (σ₂.rcns i = Reaction.relay src dst) ∧ ∀ j, j ≠ i → σ₁.rcns j = σ₂.rcns j

structure deletingRelayReactions (src dst : ID) (σ₁ σ₂ : Reactor) : Prop where
  eqCmps : ∀ cmp, (cmp ≠ Cmp.rcn) → σ₁.cmp cmp = σ₂.cmp cmp
  delete : σ₁.rcns.filter' (· ≠ Reaction.relay src dst) = σ₂.rcns

structure creatingReactor (rtr : Reactor) (i : ID) (σ₁ σ₂ : Reactor) : Prop where
  eqCmps : ∀ cmp, (cmp ≠ Cmp.rtr) → σ₁.cmp cmp = σ₂.cmp cmp
  create : σ₁.nest.update i rtr = σ₂.nest

structure deletingReactor (i : ID) (σ₁ σ₂ : Reactor) : Prop where
  eqCmps : ∀ cmp, (cmp ≠ Cmp.rtr) → σ₁.cmp cmp = σ₂.cmp cmp
  create : σ₁.nest.update i none = σ₂.nest

inductive ChangeStep (rcn : ID) (σ : Reactor) : Reactor → Change → Prop 
  | port {σ' i v} :     (σ -[Cmp.prt:i    (⟨·.role, v⟩)]→ σ') → ChangeStep rcn σ σ' (Change.port i v)
  | state {σ' i v} :    (σ -[Cmp.stv:i       (λ _ => v)]→ σ') → ChangeStep rcn σ σ' (Change.state i v)
  | action {σ' i t v} : (σ -[Cmp.act:i (schedule · t v)]→ σ') → ChangeStep rcn σ σ' (Change.action i t v)
  -- | connect {σ' src dst r} :    (isRelayReactor σ r src dst) → (σ -[Cmp.rtr;r (insertingRelayReaction src dst)]→ σ') → ChangeStep rcn σ σ' (Change.connect src dst)
  -- | disconnect {σ' src dst r} : (isRelayReactor σ r src dst) → (σ -[Cmp.rtr;r (deletingRelayReactions src dst)]→ σ') → ChangeStep rcn σ σ' (Change.disconnect src dst)
  -- | create {σ' rtr i r} :                      (σ &[rcn]= r) → (σ -[Cmp.rtr;r (creatingReactor rtr i)]→ σ')          → ChangeStep rcn σ σ' (Change.create rtr i)
  -- | delete {σ' i r} :                          (σ &[rcn]= r) → (σ -[Cmp.rtr;r (deletingReactor i)]→ σ')              → ChangeStep rcn σ σ' (Change.create rtr i)
  -- Mutations are (temporarily) no-ops:
  | connect {i₁ i₂} :    ChangeStep rcn σ σ (Change.connect i₁ i₂)
  | disconnect {i₁ i₂} : ChangeStep rcn σ σ (Change.disconnect i₁ i₂)
  | create {rtr i} :     ChangeStep rcn σ σ (Change.create rtr i)
  | delete {i} :         ChangeStep rcn σ σ (Change.delete i)

notation σ₁:max " -[" rcn ":" c "]→ " σ₂:max => ChangeStep rcn σ₁ σ₂ c

inductive ChangeListStep (rcn : ID) : Reactor → Reactor → List (Change) → Prop
  | nil (σ₁) : ChangeListStep rcn σ₁ σ₁ []
  | cons {σ₁ σ₂ σ₃ hd tl} : (σ₁ -[rcn:hd]→ σ₂) → (ChangeListStep rcn σ₂ σ₃ tl) → ChangeListStep rcn σ₁ σ₃ (hd::tl)

notation σ₁:max " -[" rcn ":" cs "]→* " σ₂:max => ChangeListStep rcn σ₁ σ₂ cs

-- We separate the execution into two parts, the instantaneous execution which controlls
-- how reactors execute at a given instant, and the timed execution, which includes the
-- passing of time
inductive InstStep (s : State) : State → Prop 
  | execReaction {rcn : Reaction} {i : ID} {σ} : 
    (s.rtr *[Cmp.rcn, i]= rcn) →
    (s.couldExec i) →
    (s.triggers rcn) →
    (s.rtr -[i:rcn (s.rcnInput rcn)]→* σ) →
    InstStep s ⟨σ, s.ctx.addCurrentExecuted i⟩
  | skipReaction {rcn : Reaction} {i : ID} :
    (s.rtr *[Cmp.rcn, i]= rcn) →
    (s.couldExec i) →
    (¬ s.triggers rcn) →
    InstStep s ⟨s.rtr, s.ctx.addCurrentExecuted i⟩

notation s₁:max " ⇓ᵢ " s₂:max => InstStep s₁ s₂

-- An execution at an instant is a series of steps,
-- which we model with the transitive closure.
inductive InstExecution : State → State → Prop 
  | single {s₁ s₂} : s₁ ⇓ᵢ s₂ → InstExecution s₁ s₂
  | trans {s₁ s₂ s₃} : s₁ ⇓ᵢ s₂ → InstExecution s₂ s₃ → InstExecution s₁ s₃

notation s₁:max " ⇓ᵢ+ " s₂:max => InstExecution s₁ s₂

abbrev State.instComplete (s : State) : Prop := s.ctx.currentExecutedRcns = s.rtr.ids Cmp.rcn

structure CompleteInstExecution (s₁ s₂ : State) : Prop where
  exec : s₁ ⇓ᵢ+ s₂
  complete : s₂.instComplete

notation s₁:max " ⇓ᵢ| " s₂:max => CompleteInstExecution s₁ s₂

def clearingPorts (σ₁ σ₂ : Reactor) : Prop := sorry -- TODO: Define this via MultiUpdate if that is realized.
theorem clearingPorts_unique {σ σ₁ σ₂ : Reactor} : clearingPorts σ σ₁ → clearingPorts σ σ₂ → σ₁ = σ₂ :=  sorry

-- Now we define a fully timed step, which can be a full instaneous execution, i.e. until no more
-- steps can be taken, or a time advancement.
inductive Step (s : State) : State → Prop 
  | completeInst (s') : s ⇓ᵢ| s' → Step s s'
  | advanceTime {σ} {g : Time.Tag} (hg : s.nextTag = g) :
    (s.instComplete) →
    (clearingPorts s.rtr σ) →
    Step s ⟨σ, s.ctx.advanceTime g $ s.time_lt_nextTag hg⟩

notation s₁:max " ⇓ " s₂:max => Step s₁ s₂

end Execution

open Execution

-- An execution of a reactor model is a series of execution steps.
-- We model this with a reflexive transitive closure:
inductive Execution : State → State → Prop
  | refl (s) : Execution s s
  | step (s₁) {s₂} (s₃) : s₁ ⇓ s₂ → Execution s₂ s₃ → Execution s₁ s₃

notation s₁ " ⇓* " s₂ => Execution s₁ s₂