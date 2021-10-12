import ReactorModel.Mathlib.Tactics
import ReactorModel.Finmap

-- The class of types that can be used as identifiers for components in a reactor.
-- 
-- IDs tend to require a "context" in order to associate them to actual objects. 
-- This context is usually a (top-level) reactor, which is then identified by the `root` value.
class ID (α) where
  root : α
  decEq : DecidableEq α

notation "⊤" => ID.root

instance ID.DecidableEq {ι} [ID ι] : DecidableEq ι := ID.decEq

-- The class of types that can be used as values in a reactor.
class Value (α) where
  absent : α
  decEq : DecidableEq α

notation "⊥" => Value.absent

instance Value.DecidableEq {υ} [Value υ] : DecidableEq υ := Value.decEq

variable (ι υ) [ID ι] [Value υ]

abbrev StateVars := ι ▸ υ

instance : Inhabited (StateVars ι υ) where
  default := (Inhabited.default : Finmap _ _)

def Ports := ι ▸ υ

instance : Inhabited (Ports ι υ) where
  default := (Inhabited.default : Finmap _ _)

namespace Ports

variable {ι υ}

-- Port roles are used to differentiate between input and output ports.
-- This is useful for avoiding duplication of definitions that are fundamentally the same 
-- and only differ by the kinds of ports that are referenced/affected.
inductive Role 
  | «in» 
  | out

instance : DecidableEq Role := λ r₁ r₂ =>
  match r₁, r₂ with
  | Role.in,  Role.in =>  Decidable.isTrue rfl 
  | Role.out, Role.out => Decidable.isTrue rfl
  | Role.in,  Role.out => Decidable.isFalse (by simp)
  | Role.out, Role.in =>  Decidable.isFalse (by simp)

@[reducible]
def Role.opposite : Role → Role 
  | Role.in => Role.out
  | Role.out => Role.in

-- A lookup method for ports, where the absent value is treated as the absence of a value.
--
-- Since ports are just finmaps, they inherit its `lookup` function.
-- As a result, if a given port `i` contains the absent value (`⊥`), then `p.lookup i = some ⊥`.
-- In many definitions we only care to differentiate between two cases though:
--
-- (1) `p.lookup i = some v` with `v ≠ ⊥`.
-- (2) `p.lookup i = some ⊥` or `p.lookup i = none`.
-- 
-- The `get` function provides this case separation by mapping `some ⊥` to `none`.
-- That is, if `p.get i = some v`, we know `v ≠ ⊥`.
def get (p : Ports ι υ) (i : ι) : Option υ := 
  p.lookup i >>= (λ v => if v = ⊥ then none else v)

notation p:max "[" i "]" => get p i

theorem eqLookupEqGet {p₁ p₂ : Ports ι υ} {i : ι} (h : p₁.lookup i = p₂.lookup i) :
  p₁[i] = p₂[i] := by
  simp [get, bind, h]

theorem lookupNoneGetNone {p : Ports ι υ} {i : ι} (h : p.lookup i = none) : p[i] = none := by
  simp [get, h]

theorem lookupAbsentAtNone {p : Ports ι υ} {i : ι} (h : p.lookup i = some ⊥) :
  p[i] = none := by
  simp [get, bind, Option.bind, h]

-- Two port-assignments are `eqAt` IDs `is`, if their values correspond for all of the given IDs.
@[reducible]
def eqAt (is : Finset ι) (p₁ p₂ : Ports ι υ) : Prop := 
  ∀ i ∈ is, p₁.lookup i = p₂.lookup i

notation p:max " =[" i "] " q:max => eqAt i p q

-- (For a fixed set of IDs) `eqAt` is an equivalence relation.
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

-- The (finite) set of IDs for which a given port-assignment contains non-absent values.
noncomputable def inhabitedIDs (p : Ports ι υ) : Finset ι :=
  let description : Set ι := { i | p[i] ≠ none }
  let finite : description.finite := by
    let f : Finset ι := p.ids.filter (λ i => p[i] ≠ none)
    suffices h : description ⊆ ↑f 
      from Set.finite.subset (Finset.finite_to_set _) h
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