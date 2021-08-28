import ReactorModel.Components.Reactor

open Reactor
open Reactor.Ports

variable {ι υ} [ID ι] [Value υ]

noncomputable def Finmap.portIDs (rtrs : ι ▸ Reactor ι υ) (r : Ports.Role) : Finset ι :=
  rtrs.values.bUnion (λ x => (x.ports r).ids)

variable (ι υ)

structure Network where
  rtrs : ι ▸ Reactor ι υ
  cns : Finset (Connection ι) 
  wfCns : ∀ c, c ∈ cns → (c.src ∈ rtrs.portIDs Role.out) ∧ (c.dst ∈ rtrs.portIDs Role.in)
  uniquePortIns : ∀ c₁ c₂, c₁ ∈ cns → c₂ ∈ cns → c₁.dst = c₂.dst → c₁ = c₂
  wfIDs : false -- !!!

variable {ι υ}

def Reactor.nest (rtr : Reactor ι υ) : Network ι υ := sorry