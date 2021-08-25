import ReactorModel.Components.MutationOutput

open Reactor
open Reactor.Ports

variable (ι υ) [ID ι] [Value υ]

structure Mutation where
  deps : Ports.Role → Finset ι 
  triggers : Finset ι
  body : Ports ι υ → StateVars ι υ → MutationOutput ι υ
  tsSubInDeps : triggers ⊆ deps Role.in
  inDepOnly : ∀ {i i'} s, (i =[deps Role.in] i') → body i s = body i' s
  outDepOnly : ∀ i s {o}, (o ∉ deps Role.out) → (body i s).prtVals[o] = none 

variable {ι υ}

def Reactor.muts (rtr : Reactor ι υ) : ι ▸ Mutation ι υ := 
  rtr.raw.muts.map (λ m => {
      deps := m.deps,
      triggers := m.triggers,
      body := (λ p s => {
          prtVals := (m.body p s).prtVals,
          state   := (m.body p s).state,
          newCns  := (m.body p s).newCns,
          delCns  := (m.body p s).delCns,
          newRtrs := (m.body p s).newRtrs.map (λ r => {
              raw := r,
              wf := sorry
            }
          ),
          delRtrs := (m.body p s).delRtrs,
        }
      ),
      tsSubInDeps := sorry,
      inDepOnly := sorry,
      outDepOnly := sorry
    }
  )

namespace Mutation

instance : CoeFun (Mutation ι υ) (λ _ => Ports ι υ → StateVars ι υ → MutationOutput ι υ) where
  coe m := m.body

def triggersOn (m : Mutation ι υ) (p : Ports ι υ) : Prop :=
  ∃ (t : ι) (v : υ), t ∈ m.triggers ∧ p[t] = some v

end Mutation