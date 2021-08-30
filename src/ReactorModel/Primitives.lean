import ReactorModel.Mathlib.Tactics
import ReactorModel.Finmap

class ID (α) where
  root : α
  decEq : DecidableEq α

notation "⊤" => ID.root

instance ID.DecidableEq {ι} [ID ι] : DecidableEq ι := ID.decEq

class Value (α) where
  absent : α
  decEq : DecidableEq α

notation "⊥" => Value.absent

instance Value.DecidableEq {υ} [Value υ] : DecidableEq υ := Value.decEq

variable (ι υ) [ID ι] [Value υ]

namespace Reactor

abbrev StateVars := ι ▸ υ

instance : Inhabited (StateVars ι υ) where
  default := (Inhabited.default : Finmap _ _)

def Ports := ι ▸ υ

instance : Inhabited (Ports ι υ) where
  default := (Inhabited.default : Finmap _ _)

namespace Ports

variable {ι υ}

inductive Role 
  | «in» 
  | out

@[reducible]
def Role.opposite : Role → Role 
  | Role.in => Role.out
  | Role.out => Role.in

def get (p : Ports ι υ) (i : ι) : Option υ := 
  p.lookup i >>= (λ v => if v = ⊥ then none else v)

notation p "[" i "]" => get p i

theorem eqLookupEqGet {p₁ p₂ : Ports ι υ} {i : ι} (h : p₁.lookup i = p₂.lookup i) :
  p₁[i] = p₂[i] := by
  simp [get, bind, h]

theorem lookupNoneGetNone {p : Ports ι υ} {i : ι} (h : p.lookup i = none) : p[i] = none := by
  simp [get, h]

theorem lookupAbsentAtNone {p : Ports ι υ} {i : ι} (h : p.lookup i = some ⊥) :
  p[i] = none := by
  simp [get, bind, Option.bind, h]

@[reducible]
def eqAt (is : Finset ι) (p₁ p₂ : Ports ι υ) : Prop := 
  ∀ i ∈ is, p₁.lookup i = p₂.lookup i

notation p " =[" i "] " q => eqAt i p q

instance eqAt.Setoid (is : Finset ι) : Setoid (Ports ι υ) := { 
  r := eqAt is,
  iseqv := { 
    refl := by
      simp only [eqAt]
      intro x i hi
      rfl
    symm := by
      simp only [eqAt]
      intro x y h i hi
      apply Eq.symm
      exact h i hi
    trans := by
      simp only [eqAt]
      intro x y z hxy hyz i hi
      exact Eq.trans (hxy i hi) (hyz i hi)
  }
}

def mergeOnto (src dst : Ports ι υ) : Ports ι υ := {
  lookup := λ i => src[i] <|> dst.lookup i,
  finite := by
    suffices h : { i | (λ j => src[j] <|> dst.lookup j) i ≠ none } ⊆ ↑(src.ids ∪ dst.ids) by
      exact Set.finite.subset (Finset.finite_to_set (src.ids ∪ dst.ids)) h
    simp [Set.subset_def]
    intro x h
    simp [Finmap.idsDef]
    byContra hc
    rw [←and_iff_not_or_not] at hc
    rw [hc.right, Option.orelse_none, lookupNoneGetNone hc.left] at h
    contradiction
} 

noncomputable def inhabitedIDs (p : Ports ι υ) : Finset ι :=
  let description : Set ι := { i | p[i] ≠ none }
  let finite : description.finite := by
    let f : Finset ι := p.ids.filter (λ i => p[i] ≠ none)
    suffices h : description ⊆ ↑f by 
      exact Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
    intro x h
    simp at *
    split
    case right => exact h
    case left =>
      rw [Finmap.idsDef]
      simp [get, Option.ne_none_iff_exists] at h
      obtain ⟨_, ⟨_, ⟨h, _⟩⟩⟩ := h
      simp [Option.ne_none_iff_exists, h]
  finite.toFinset

theorem inhabitedIDsNone {p : Ports ι υ} {i : ι} (h : p[i] = none) : i ∉ p.inhabitedIDs := by
  simp only [inhabitedIDs, Set.finite.mem_to_finset, setOf]
  simp [h, Mem.mem, Set.mem]

end Ports

end Reactor