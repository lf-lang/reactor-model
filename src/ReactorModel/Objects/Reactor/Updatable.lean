import ReactorModel.Objects.Reactor.WellFounded

open Reactor (Component)

namespace ReactorType

-- TODO: Find a better name for this.
def RootEqualUpTo [ReactorType α] (cpt : Component) (i : ID) (rtr₁ rtr₂ : α) : Prop :=
  ∀ {c j}, (c ≠ cpt ∨ j ≠ i) → cpt? c rtr₁ j = cpt? c rtr₂ j

-- TODO: Move this to the Theorems folder.
namespace RootEqualUpTo

variable [ReactorType α] in section 

theorem mem_iff {rtr₁ : α} (e : RootEqualUpTo cpt i rtr₁ rtr₂) 
    (h : c ≠ cpt ∨ j ≠ i) : (j ∈ cpt? c rtr₁) ↔ (j ∈ cpt? c rtr₂) := by
  simp [Partial.mem_iff]
  exact ⟨(e h ▸ ·), (e h ▸ ·)⟩   

theorem symm {rtr₁ : α} (e : RootEqualUpTo cpt i rtr₁ rtr₂) :
    RootEqualUpTo cpt i rtr₂ rtr₁ :=
  (e · |>.symm)

theorem trans {rtr₁ : α} (e₁ : RootEqualUpTo cpt i rtr₁ rtr₂)
    (e₂ : RootEqualUpTo cpt i rtr₂ rtr₃) : RootEqualUpTo cpt i rtr₁ rtr₃ :=
  fun h => (e₁ h).trans (e₂ h)

end

set_option hygiene false in
scoped macro "ext_cpt_proof " cpt:ident : tactic => `(tactic|
  (
    let i : ID := ‹_› 
    ext1 j
    cases cpt <;> try cases ‹Component.Valued›
    case $cpt:ident => 
      by_cases hi : j = i 
      case pos => exact hi ▸ ‹cpt? _ _ _ = cpt? _ _ _›  
      case neg => exact e (c := .$cpt) (.inr hi) 
    all_goals exact e (c := .$cpt) (.inl $ by simp) 
  )
)

protected theorem ext [Extensional α] {rtr₁ : α} (e : RootEqualUpTo cpt i rtr₁ rtr₂)
    (h : cpt? cpt rtr₁ i = cpt? cpt rtr₂ i) : rtr₁ = rtr₂ := by
  ext
  case _ =>
    split_ands
    rotate_left
    · ext_cpt_proof act 
    · ext_cpt_proof stv
    · ext_cpt_proof rcn
    · ext_cpt_proof rtr
    · funext k j
      cases k
      case «in» =>
        cases cpt <;> try cases ‹Component.Valued› <;> try cases ‹Kind›
        case prt.in => 
          by_cases hi : j = i 
          case pos => exact hi ▸ ‹cpt? _ _ _ = cpt? _ _ _›  
          case neg => exact e (c := .prt .in) (.inr hi) 
        all_goals exact e (c := .prt .in) (.inl $ by simp) 
      case «out» =>
        cases cpt <;> try cases ‹Component.Valued› <;> try cases ‹Kind›
        case prt.out => 
          by_cases hi : j = i 
          case pos => exact hi ▸ ‹cpt? _ _ _ = cpt? _ _ _›  
          case neg => exact e (c := .prt .out) (.inr hi) 
        all_goals exact e (c := .prt .out) (.inl $ by simp) 

end RootEqualUpTo

variable [ReactorType α]

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