inductive priority
| star : priority
| mk (z : ℤ) (h : z ≠ 0) : priority

variables p₁ p₂ : priority

namespace priority

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

-- def priority_set := set prio

end priority
