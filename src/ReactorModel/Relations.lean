namespace Relations
universe u 
def relation (X : Type u) := X → X → Prop

inductive multi {X : Type u} (R : relation X) : X → X → Prop
 | multi_refl : ∀ (x : X), multi R x x
 | multi_step : ∀ (x y z : X), R x y → multi R y z → multi R x z

end Relations