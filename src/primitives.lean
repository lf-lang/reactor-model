import data.rel

-- The type of opaque values that can be passed between reactors and processed by reactions.
-- Their equality has to be decidable, but beyond that their values are of no interest. Hence they
-- are modeled as `empty`.
def value := empty

namespace rel

  def is_function {α β : Type*} (r : rel α β) : Prop :=
    ∀ a : α, ∃! b : β, r a b

  noncomputable def function {α β : Type*} (r : rel α β) (h : r.is_function) : α → β :=
    λ a : α, (h a).some 

end rel