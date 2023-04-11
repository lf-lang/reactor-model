import ReactorModel.Objects.Reactor.Basic

namespace ReactorType

variable [ReactorType α]

-- Note: Without ID-uniqueness this can be satisfied by updating exactly one of the occurrences of
--       the target. Since we have a choice of which target we update, this type isn't a `Prop`. 
--       (We need to be able to eliminate into `Type` in `Member.fromLawfulUpdate`).
inductive LawfulMemUpdate (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) : α → α → Type
  | final : 
    (rtr₁ ≃[cpt][i] rtr₂) → (rtr₁{cpt}{i} = some o) → (rtr₂{cpt}{i} = f o) → 
    LawfulMemUpdate cpt i f rtr₁ rtr₂
  | nested : 
    (rtr₁ ≃[.rtr][j] rtr₂) → (rtr₁{.rtr}{j} = some n₁) → (rtr₂{.rtr}{j} = some n₂) → 
    (LawfulMemUpdate cpt i f n₁ n₂) → LawfulMemUpdate cpt i f rtr₁ rtr₂

-- Note: This isn't a `Prop` because of the explanation on `LawfulMemUpdate`.
inductive LawfulUpdate (cpt : Component.Valued) (i : ID) (f : cpt.type → cpt.type) (rtr₁ rtr₂ : α)
  | update (u : LawfulMemUpdate cpt i f rtr₁ rtr₂)
  | notMem (h : IsEmpty $ Member cpt i rtr₁) (eq : rtr₁ = rtr₂)

class Updatable (α) extends ReactorType α where
  update : α → (cpt : Component.Valued) → ID → (cpt.type → cpt.type) → α  
    
class LawfulUpdatable (α) extends Updatable α where 
  lawful : ∀ rtr cpt i f, LawfulUpdate cpt i f rtr (update rtr cpt i f)      

end ReactorType