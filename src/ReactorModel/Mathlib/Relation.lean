def Relation (α) := α → α → Prop

namespace Relation

inductive transClosure (r : Relation α) : α → α → Prop
  | base {a₁ a₂ : α} : r a₁ a₂ → transClosure r a a
  | trans {a₁ a₂ a₃ : α} : transClosure r a₁ a₂ → transClosure r a₂ a₃ → transClosure r a₁ a₃

end Relation