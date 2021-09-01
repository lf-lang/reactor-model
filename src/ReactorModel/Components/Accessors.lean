import ReactorModel.Components.Network

variable {ι υ} [ID ι] [Value υ]

inductive Cmp -- "Component"
  | rtr
  | rcn
  | «mut»
  | prt
  | stateVar

variable (ι υ)

def Cmp.type : Cmp → Type _ 
  | rtr      => Reactor ι υ
  | rcn      => Reaction ι υ
  | «mut»    => Mutation ι υ
  | prt      => Ports ι υ
  | stateVar => StateVars ι υ

namespace Reactor

variable {ι υ}

def containerOf (rtr : Reactor ι υ) (cmp : Cmp) (i : ι) : Option ι := 
  sorry

notation r " &[" c "] " i => Reactor.containerOf r c i

def cmp (rtr : Reactor ι υ) (cmp : Cmp) (i : ι) : Option (cmp.type ι υ) :=
  match cmp with
  | Cmp.rtr => sorry
  | Cmp.rcn => sorry
  | Cmp.«mut» => sorry
  | Cmp.prt => sorry
  | Cmp.stateVar => sorry

notation r " *[" c "] " i => Reactor.cmp r c i

noncomputable def allIDsFor (rtr : Reactor ι υ) (cmp : Cmp) : Finset ι := 
  let description := {i | (rtr *[cmp] i) ≠ none}
  let finite : description.finite := sorry
  finite.toFinset

notation η "&[" c "]" => Reactor.allIDsFor η c

end Reactor