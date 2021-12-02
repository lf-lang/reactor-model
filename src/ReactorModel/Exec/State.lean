import ReactorModel.Time
import ReactorModel.Components

open Reactor Ports Classical Time

namespace State
variable {ι υ} [Value υ]

structure State where
  time : Tag
  ports : ι ▸  υ
  reactions : ι ▸  υ
  actions : ι ▸ (Tag × υ)

-- We used the same recursive structure to show that a state is well-formed 
structure stateDirectlyWF (s : @State ι υ) (r : Reactor ι υ) : Prop where
  portsComplete : forall i, r.ports[i] ≠ none → s.ports i  ≠ none
  reactorsComplete : forall i, r.rcns i ≠ none → s.reactions i  ≠ none 
  --actionsComplete : forall i,  r.actions → s.actions i  ≠ none
  reactorsCorrect : forall i v, s.reactions i = some v → (v = ⊥ ∨ v = (⊤ : υ))
  --actionsCorrect : forall i g v, s.actions i = some (g,v) → s.time < g

structure stateWellFormed (s : State) (r : Reactor ι υ) : Prop where
  direct : ( stateDirectlyWF s r)
  offspring : ∀ {rtr : Reactor ι υ}, isAncestorOf r rtr → stateDirectlyWF s rtr 

end State