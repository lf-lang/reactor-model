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
  p.at i = p'.at i := by sorry
  -- simp only [«at», h]

lemma at'AbsentAtNone {p : Ports ι υ} {i : ι} (h : p.at' i = some ⊥) :
  p.at i = none := by sorry
  -- simp [«at», h]

@[reducible]
def eqAt (is : Finset ι) (p p' : Ports ι υ) : Prop := 
  ∀ i ∈ is, p.at' i = p'.at' i

notation p " =" i "= " q => eqAt i p q

instance eqAt.Setoid (is : Finset ι) : Setoid (Ports ι υ) := { 
  r := eqAt is,
  iseqv := ⟨
    by sorry, -- tauto,
    by sorry, -- tauto,
    by sorry -- { simp only [transitive, eqAt]; finish }
  ⟩
}

noncomputable def mergeOnto («from» «to» : Ports ι υ) : Ports ι υ :=
  let description := ∃ result : Ports ι υ, result.ids = to.ids ∧ (∀ i ∈ result.ids, result.at i = (from.at i <|> to.at i))
  let existence : description := sorry
  Classical.choose existence

noncomputable def inhabitedIDs (p : Ports ι υ) : Finset ι :=
  let description : Set ι := { i | p.at i ≠ none }
  let isFinite : description.finite := sorry
      /-let f : finset ι := p.ids.filter (λ i => p.at i ≠ none)
      suffices h : ↑f = description by simp only [←h, finset.finite_to_set]
      ext
      split
        {
          intro h,
          simp only [set.mem_sep_eq, finset.mem_range, finset.mem_coe, finset.coe_filter] at h,
          simp only [h, ne.def, not_false_iff, set.mem_set_of_eq]
        },
        {
          intro h,
          simp only [set.mem_set_of_eq] at h,
          have h', from h,
          simp only [«at», Option.ne_none_iff_exists] at h',
          obtain ⟨_, h'⟩ := h',
          replace h' := eq.symm h',
          simp [Option.bind_eq_some] at h',
          obtain ⟨_, ⟨h', _⟩⟩ := h',
          simp only [at'] at h',
          have h'', from finmap.mem_of_lookup_eq_some h',
          simp only [set.mem_sep_eq, finset.mem_coe, finset.coe_filter],
          exact ⟨h'', h ⟩
        }-/
  isFinite.toFinset

lemma inhabitedIDsNone {p : Ports ι υ} {i : ι} (h : p.at i = none) : i ∉ p.inhabitedIDs :=
  by sorry
  -- simp [inhabitedIDs, h]

end Ports

end Reactor