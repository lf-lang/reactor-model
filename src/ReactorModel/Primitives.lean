import ReactorModel.Mathlib

class Reactor.Value (α) := 
  (absent : α)
  (decEq : DecidableEq α)

notation "⊥" => Reactor.Value.absent

instance Reactor.Value.DecidableEq {υ} [Reactor.Value υ] : DecidableEq υ := Reactor.Value.decEq

variable (ι υ) [DecidableEq ι] [Reactor.Value υ]

namespace Reactor

def StateVars := ι ⇀ υ

def Ports := ι ⇀ υ

namespace Ports

variable {ι υ}

inductive Role 
  | «in» 
  | out

@[reducible]
def Role.opposite : Role → Role 
  | Role.in => Role.out
  | Role.out => Role.in

def at' (p : Ports ι υ) (i : ι) : Option υ := 
  p.lookup i

def «at» (p : Ports ι υ) (i : ι) : Option υ := 
  p.at' i >>= (λ v => if v = ⊥ then none else v)

theorem at'ToAt {p p' : Ports ι υ} {i : ι} (h : p.at' i = p'.at' i) :
  p.at i = p'.at i := by
  simp [«at», bind, h]
  
theorem at'AbsentAtNone {p : Ports ι υ} {i : ι} (h : p.at' i = some ⊥) :
  p.at i = none := by
  simp [«at», bind, Option.bind, h]

@[reducible]
def eqAt (is : Finset ι) (p p' : Ports ι υ) : Prop := 
  ∀ i ∈ is, p.at' i = p'.at' i

notation p " =" i "= " q => eqAt i p q

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

noncomputable def mergeOnto («from» «to» : Ports ι υ) : Ports ι υ :=
  let description := ∃ result : Ports ι υ, result.ids = to.ids ∧ (∀ i ∈ result.ids, result.at i = (from.at i <|> to.at i))
  let existence : description := sorry
  Classical.choose existence

noncomputable def inhabitedIDs (p : Ports ι υ) : Finset ι :=
  let description : Set ι := { i | p.at i ≠ none }
  let isFinite : description.finite := by
    let f : Finset ι := p.ids.filter (λ i => p.at i ≠ none)
    suffices h : ↑f = description by 
      rw [←h]
      simp only [Finset.finite_to_set]
    apply Set.ext
    intro x
    split
    focus
      intro h
      simp only [Set.mem_sep_eq, Finset.mem_range, Finset.mem_coe, Finset.coe_filter] at h
      simp only [h, Ne.def, not_false_iff, Set.mem_set_of_eq]
    focus
      intro h
      simp only [Set.mem_set_of_eq] at h
      have h' := h
      simp only [«at», Option.ne_none_iff_exists] at h'
      obtain ⟨_, h'⟩ := h'
      have h' := Eq.symm h'
      simp [Option.bind_eq_some] at h'
      obtain ⟨_, ⟨h', _⟩⟩ := h'
      simp only [at'] at h'
      have h'' := Finmap.mem_of_lookup_eq_some h'
      simp only [Set.mem_sep_eq, Finset.mem_coe, Finset.coe_filter, Finmap.ids, Finmap.mem_keys]
      exact ⟨h'', h⟩
  isFinite.toFinset

theorem inhabitedIDsNone {p : Ports ι υ} {i : ι} (h : p.at i = none) : i ∉ p.inhabitedIDs := by
  simp only [inhabitedIDs, Set.finite.mem_to_finset, setOf]
  simp [h, Mem.mem, Set.mem]

end Ports

end Reactor