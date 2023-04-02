import ReactorModel.Objects
import Mathlib.Data.Finset.Lattice

noncomputable section
open Classical
open ReactorType Updatable Indexable

def Action.schedule (a : Action) (t : Time) (v : Value) : Action :=
  match a.tags.filter (·.time = t) |>.max with
  | ⊥           => a.insert ⟨t, 0⟩ v
  | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

namespace ReactorType
namespace Updatable

variable [Updatable α] 

def apply (rtr : α) : Change → α 
  | .prt k i v => update rtr (.prt k) i (fun _ => v)
  | .stv i v   => update rtr .stv     i (fun _ => v)
  | .act i t v => update rtr .act     i (·.schedule t v)
  | .mut ..    => rtr -- Mutations are currently no-ops.

def apply' (rtr : α) (cs : List Change) : α :=
  cs.foldl apply rtr

end Updatable

namespace Indexable

variable [Indexable α] 

def dependencies (rtr : α) (rcn : ID) : Set ID := 
  { rcn' | rcn' <[rtr] rcn }

theorem equiv_eq_dependencies {rtr₁ : α} (e : rtr₁ ≈ rtr₂) : 
  dependencies rtr₁ = dependencies rtr₂ := by
  ext i j
  exact ⟨.equiv $ .symm e, .equiv e⟩ 

def scheduledTags (rtr : α) : Set Time.Tag := 
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.keys) }

-- TODO?: Make this handle tag names better.
scoped macro "change_cases " change:term : tactic => 
  `(tactic| cases $change:term <;> try cases ‹Change.Normal›; cases ‹Reactor.Component.Valued›)

theorem apply_equiv (rtr : α) (c : Change) : (apply rtr c) ≈ rtr := by
  change_cases c <;> first | rfl | apply LawfulUpdatable.equiv

theorem apply_preserves_unchanged {c : Change} (rtr : α) (h : ¬c.Targets cpt i) :
    (apply rtr c)[cpt][i] = rtr[cpt][i] := by
  change_cases c <;> first | rfl | exact LawfulUpdatable.obj?_preserved (Change.Targets.norm_not h)

variable {rtr : α}

theorem apply_port_change (h : i ∈ rtr[.prt k]) : (apply rtr $ .prt k i v)[.prt k][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_state_change (h : i ∈ rtr[.stv]) : (apply rtr $ .stv i v)[.stv][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_action_change (h : rtr[.act][i] = some a) : 
    (apply rtr $ .act i t v)[.act][i] = some (a.schedule t v) := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact ⟨_, ⟨h, rfl⟩⟩ 

theorem apply'_equiv (rtr : α) : (cs : List Change) → (apply' rtr cs) ≈ rtr 
  | .nil        => .refl
  | .cons hd tl => Equivalent.trans (apply'_equiv (apply rtr hd) tl) (apply_equiv rtr hd)

theorem apply'_preserves_unchanged {cs : List Change} {cpt : Reactor.Component.Valued} {i}
    (h : cs.All₂ (¬·.Targets cpt i)) : (apply' rtr cs)[cpt][i] = rtr[cpt][i] := by
  induction cs generalizing rtr <;> try rfl
  case cons hd tl hi => 
    have ⟨hh, ht⟩ := List.all₂_cons _ _ _ |>.mp h
    exact apply_preserves_unchanged rtr hh ▸ hi ht 

-- TODO: This theorem is false. What we need in the changes' underlying cpts to be disjoint. 
theorem apply'_normal_disjoint_comm 
    (h : List.Disjoint (cs₁.filter (·.IsNormal)) (cs₂.filter (·.IsNormal))) : 
    apply' (apply' rtr cs₁) cs₂ = apply' (apply' rtr cs₂) cs₁ :=
  sorry

end Indexable
end ReactorType