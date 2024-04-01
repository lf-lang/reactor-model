import ReactorModel.Objects.Reactor.Basic

namespace Reactor

variable [Reactor α]

-- Note: Without ID-uniqueness this can be satisfied by updating exactly one of the occurrences of
--       the target. Since we have a choice of which target we update, this type isn't a `Prop`. 
--       (We need to be able to eliminate into `Type` in `Member.fromLawfulUpdate`).
inductive LawfulMemUpdate (cpt : Component.Valued) (i : ID) (v : Value) : α → α → Type
  | final : 
    (rtr₁ ≃[cpt][i] rtr₂) → (rtr₁{cpt}{i} = some o) → (rtr₂{cpt}{i} = v) → 
    LawfulMemUpdate cpt i v rtr₁ rtr₂
  | nested : 
    (rtr₁ ≃[.rtr][j] rtr₂) → (rtr₁{.rtr}{j} = some n₁) → (rtr₂{.rtr}{j} = some n₂) → 
    (LawfulMemUpdate cpt i v n₁ n₂) → LawfulMemUpdate cpt i v rtr₁ rtr₂

-- Note: This isn't a `Prop` because of the explanation on `LawfulMemUpdate`.
inductive LawfulUpdate (cpt : Component.Valued) (i : ID) (v : Value) (rtr₁ rtr₂ : α)
  | update (u : LawfulMemUpdate cpt i v rtr₁ rtr₂)
  | notMem (h : IsEmpty $ Member cpt i rtr₁) (eq : rtr₁ = rtr₂)

class Updatable (α) extends Reactor α where
  update : α → (cpt : Component.Valued) → ID → Value → α  
    
class LawfulUpdatable (α) extends Updatable α where 
  lawful : ∀ rtr cpt i v, LawfulUpdate cpt i v rtr (update rtr cpt i v)      

end Reactor