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

notation p "[" i "]'" => Finmap.lookup p i

def get (p : Ports ι υ) (i : ι) : Option υ := 
  p[i]' >>= (λ v => if v = ⊥ then none else v)

notation p "[" i "]" => get p i

theorem lookupToGet {p₁ p₂ : Ports ι υ} {i : ι} (h : p₁[i]' = p₂[i]') :
  p₁[i] = p₂[i] := by
  simp [get, bind, h]
  
theorem lookupAbsentAtNone {p : Ports ι υ} {i : ι} (h : p[i]' = some ⊥) :
  p[i] = none := by
  simp [get, bind, Option.bind, h]

@[reducible]
def eqAt (is : Finset ι) (p₁ p₂ : Ports ι υ) : Prop := 
  ∀ i ∈ is, p₁[i]' = p₂[i]'

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

noncomputable def mergeOnto (src dst : Ports ι υ) : Ports ι υ :=
  let description := ∃! result : Ports ι υ, result.ids = dst.ids ∧ (∀ i ∈ result.ids, result[i] = (src[i] <|> dst[i]))
  let existence : description := sorry
  Classical.choose existence

noncomputable def inhabitedIDs (p : Ports ι υ) : Finset ι :=
  let description : Set ι := { i | p[i] ≠ none }
  let isFinite : description.finite := by
    let f : Finset ι := p.ids.filter (λ i => p[i] ≠ none)
    suffices h : ↑f = description by 
      simp only [←h, Finset.finite_to_set]
    apply Set.ext
    intro x
    split
    focus
      intro h
      simp only [Set.mem_sep_eq, Finset.mem_range, Finset.mem_coe, Finset.coe_filter] at h
      simp only [h, Ne.def, not_false_iff, Set.mem_set_of_eq]
    focus
      simp only [Set.mem_set_of_eq] at h
      have h' := h
      simp only [get, Option.ne_none_iff_exists] at h'
      obtain ⟨_, h'⟩ := h'
      sorry
    sorry
      /-have h' := Eq.symm h'
      simp [Option.bind_eq_some] at h'
      obtain ⟨_, ⟨h', _⟩⟩ := h'
      simp only [at'] at h'
      simp [Set.mem_sep_eq, Finset.mem_coe, Finset.coe_filter]
      split
      focus
        apply Finset.mem_coe.mp
        simp [Finmap.idsDef, Set.mem_set_of_eq, h']
      focus
        exact h-/
  isFinite.toFinset

theorem inhabitedIDsNone {p : Ports ι υ} {i : ι} (h : p[i] = none) : i ∉ p.inhabitedIDs := by
  simp only [inhabitedIDs, Set.finite.mem_to_finset, setOf]
  simp [h, Mem.mem, Set.mem]

end Ports

end Reactor