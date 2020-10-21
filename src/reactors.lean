namespace priority

-- Definition 5
inductive priority : Type
| star : priority
| mk (z : ℤ) (h : z ≠ 0) : priority

variables p₁ p₂ : priority

-- Definition 5
include p₁ p₂
protected def le : Prop := 
begin
    cases p₁ with z₁,      --| p₁ p₂ 
        cases p₂ with z₂,  --| 
            exact true,    --| *  * 
            exact z₂ > 0,  --| *  ℤ
        cases p₂ with z₂,  --|
            exact z₁ < 0,  --| ℤ  *
            exact z₁ ≤ z₂  --| ℤ  ℤ
end

instance : has_le priority := ⟨priority.le⟩ 

-- Definition 5
def priority_set := set priority

end priority

namespace action

-- Definition 6
structure action (I O : Type*) :=
(action_identifier : I)
(delay : ℕ)
(origin : O)

variables {I O : Type*}
variable a : action I O

--! Actually the delay should be gotten from the identifier alone. 
--! But since that would require some kind of central database to get an action from its identifier,
--! we also require the action implicitly, as well as a proof that the given identifier matches that action's identifier.
def d {a : action I O} (x : I) (h: a.action_identifier = x) : ℕ := a.delay

--! Cf. `d` above.
def o {a : action I O} (x : I) (h: a.action_identifier = x) : O := a.origin

end action

-- Definition 7
structure reactor (Sigma A S N M R G P Dot Caro : Type*) :=
(inputs : set.subset Sigma)
(outputs: set.subset Sigma)