import ReactorModel.Objects.Reactor.WellFounded

open Reactor (Component)

namespace ReactorType

variable [ReactorType α] [ReactorType β]

-- TODO: Find a better name for this.
def RootEqualUpTo (cpt : Component) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cpt ∨ j ≠ i) → cpt? c rtr₁ j = cpt? c rtr₂ j

theorem RootEqualUpTo.mem_iff {rtr₁ : α} (e : RootEqualUpTo cpt i rtr₁ rtr₂) 
    (h : c ≠ cpt ∨ j ≠ i) : (j ∈ cpt? c rtr₁) ↔ (j ∈ cpt? c rtr₂) := by
  simp [Partial.mem_iff]
  exact ⟨(e h ▸ ·), (e h ▸ ·)⟩   

-- Note: Without ID-uniqueness this can be satisfied by updating exactly one of the occurrences of
--       the target. Since we have a choice of which target we update, this type isn't a `Prop`. 
--       (We need to be able to eliminate into `Type` in `Member.fromLawfulUpdate`).
inductive LawfulMemUpdate (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) : α → α → Type
  | final : 
    (RootEqualUpTo cpt i rtr₁ rtr₂) → (cpt? cpt rtr₁ i = some o) → (cpt? cpt rtr₂ i = f o) → 
    LawfulMemUpdate cpt i f rtr₁ rtr₂
  | nest : 
    (RootEqualUpTo .rtr j rtr₁ rtr₂) → (cpt? .rtr rtr₁ j = some n₁) → (cpt? .rtr rtr₂ j = some n₂) → 
    (LawfulMemUpdate cpt i f n₁ n₂) → LawfulMemUpdate cpt i f rtr₁ rtr₂

-- Note: This isn't a `Prop` because of the explanation on `LawfulMemUpdate`.
inductive LawfulUpdate (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) (rtr₁ rtr₂ : α)
  | update (u : LawfulMemUpdate cpt i f rtr₁ rtr₂)
  | notMem (h : IsEmpty $ Member cpt i rtr₁) (eq : rtr₁ = rtr₂)

class Updatable (α) extends ReactorType.WellFounded α where
  update : α → (cpt : Component.Valued) → ID → (cpt.type → cpt.type) → α  
    
class LawfulUpdatable (α) extends Updatable α where 
  lawful : ∀ rtr cpt i f, LawfulUpdate cpt i f rtr (update rtr cpt i f)      

end ReactorType