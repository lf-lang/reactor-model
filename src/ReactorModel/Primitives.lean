import ReactorModel.Mathlib

open Classical

-- TODO: Add docs for Rooted.

inductive Rooted (ι)
  | root
  | nested (i : ι)

notation "⊤" => Rooted.root

instance : Coe ι (Rooted ι) where
  coe (i : ι) := Rooted.nested i

-- The class of types that can be used as values in a reactor.
-- Any such type must contain an "absent" value.
class Value (α) where
  absent : α
  unit : α

notation "⊥" => Value.absent

variable {ι υ} [Value υ]

-- Port roles are used to differentiate between input and output ports.
-- This is useful for avoiding duplication of definitions that are fundamentally 
-- the same and only differ by the kinds of ports that are referenced/affected.
--
-- E.g. a reaction defines its dependencies as a map `Port.Role → Finset ι`,
-- instead of two separate fields, each of type `Finset ι`.
inductive Port.Role
  | «in» 
  | out
deriving DecidableEq

-- When writing functions that are generic over a port's role,
-- it is sometimes necessary to talk about the "opposite" role.
--
-- E.g. when connecting ports, it might be possible to connect an
-- input to an output port, as well as an output port to an input port.
-- This can be defined generically by using the concept of an opposite role.
abbrev Port.Role.opposite : Role → Role 
  | Role.in => Role.out
  | Role.out => Role.in

namespace Finmap 

-- TODO: Remove `get`, `eqAt` and `inhabitedIDs` if they remain unused.

-- A lookup method for ports where the absent value is treated as the absence of a value.
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
--
-- The notation used for `p.get i` is `p[i]`.
noncomputable def getValue (p : ι ▸ υ) (i : ι) : Option υ := 
  p.lookup i >>= (λ v => if v = ⊥ then none else v)

notation p:max "[" i "]" => getValue p i

theorem eq_lookup_eq_getValue {p₁ p₂ : ι ▸ υ} {i : ι} (h : p₁ i = p₂ i) :
  p₁[i] = p₂[i] := by
  simp [getValue, bind, h]

theorem lookup_none_getValue_none {p : ι ▸ υ} {i : ι} (h : p i = none) : 
  p[i] = none := by
  simp only [getValue, h]
  rfl

theorem lookup_absent_getValue_none {p : ι ▸ υ} {i : ι} (h : p i = some ⊥) :
  p[i] = none := by
  simp [getValue, bind, Option.bind, h]

-- Two port-assignments are `eqAt` (equal at) a given set of IDs,
-- if their values correspond for all those IDs.
-- Note, we only require equality up to `get`, not `lookup`.
--
-- The notation used for `eqAt is p₁ p₂` is `p₁ =[is] p₂`.
def eqAt (is : Finset ι) (p₁ p₂ : ι ▸ υ) : Prop := 
  ∀ i ∈ is, p₁[i] = p₂[i]

notation p:max " =[" i "] " q:max => eqAt i p q

-- (For a fixed set of IDs) `eqAt` is an equivalence relation.
instance eqAt.Setoid (is : Finset ι) : Setoid (ι ▸ υ) := { 
  r := eqAt is,
  iseqv := { 
    refl := by simp [eqAt]
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

-- An ID "is present" in a port assignment if the port exists and has a non-absent value.
-- That is, it contains a value that is not `⊥`.
def isPresent (p : ι ▸ υ) (i : ι) : Prop :=
  p[i] ≠ none

-- The (finite) set of IDs for which a given port-assignment contains non-absent values.
noncomputable def presentIDs (p : ι ▸ υ) : Finset ι :=
  let description : Set ι := { i | p.isPresent i }
  let finite : description.finite := by
    let f : Finset ι := p.ids.filter (λ i => p[i] ≠ none)
    suffices h : description ⊆ ↑f 
      from Set.finite.subset (Finset.finite_to_set _) h
    simp [Set.subset_def]
    intro x h
    simp at *
    apply And.intro
    case right => exact h
    case left =>
      rw [Finmap.ids_def, Ne.def]
      exact mt lookup_none_getValue_none h  
  finite.toFinset

end Finmap