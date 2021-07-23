import mutation
open reactor
open reactor.ports

-- Cf. primitives.lean
variables (ι υ : Type*) [decidable_eq ι] [reactor.value υ]

structure reaction extends (mutation ι υ) :=
  (no_new_cns  : ∀ i s, (body i s).new_cns  = [])
  (no_del_cns  : ∀ i s, (body i s).del_cns  = [])
  (no_new_rtrs : ∀ i s, (body i s).new_rtrs = [])
  (no_del_rtrs : ∀ i s, (body i s).del_rtrs = ∅)

namespace reaction

  variables {ι υ}

  instance coe_to_fun : has_coe_to_fun (reaction ι υ) := ⟨_, (λ r, r.body)⟩

  def triggers_on (rcn : reaction ι υ) : ports ι υ → Prop := rcn.to_mutation.triggers_on

end reaction