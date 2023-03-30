import ReactorModel.Objects
import Mathlib.Data.Finset.Lattice

noncomputable section
open ReactorType Updatable Indexable

def Action.schedule (a : Action) (t : Time) (v : Value) : Action :=
  match a.tags.filter (·.time = t) |>.max with
  | ⊥           => a.insert ⟨t, 0⟩ v
  | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

namespace Reactor

def dependencies (rtr : Reactor) (rcn : ID) : Set ID := 
  { rcn' | rcn' <[rtr] rcn }

theorem equiv_eq_dependencies {rtr₁ : Reactor} (e : rtr₁ ≈ rtr₂) : 
    rtr₁.dependencies = rtr₂.dependencies := by
  ext i j
  exact ⟨.equiv $ .symm e, .equiv e⟩ 

def scheduledTags (rtr : Reactor) : Set Time.Tag := 
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.keys) }

def apply (rtr : Reactor) : Change → Reactor
  | .prt k i v => update rtr (.prt k) i (fun _ => v)
  | .stv i v   => update rtr .stv     i (fun _ => v)
  | .act i t v => update rtr .act     i (·.schedule t v)
  | .mut ..    => rtr -- Mutations are currently no-ops.

def apply' (rtr : Reactor) (cs : List Change) : Reactor :=
  cs.foldl apply rtr

-- TODO?: Make this handle tag names better.
scoped macro "change_cases " change:term : tactic => 
  `(tactic| cases $change:term <;> try cases ‹Change.Normal›; cases ‹Component.Valued›)

theorem apply_equiv (rtr : Reactor) (c : Change) : rtr.apply c ≈ rtr := by
  change_cases c <;> first | rfl | apply LawfulUpdatable.equiv

theorem apply_preserves_unchanged {c : Change} (rtr : Reactor) (h : ¬c.Targets cpt i) :
    (rtr.apply c)[cpt][i] = rtr[cpt][i] := by
  change_cases c <;> first | rfl | exact LawfulUpdatable.obj?_preserved (Change.Targets.norm_not h)

theorem apply_port_change {rtr : Reactor} (h : i ∈ rtr[.prt k]) : 
    (rtr.apply $ .prt k i v)[.prt k][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_state_change {rtr : Reactor} (h : i ∈ rtr[.stv]) : 
    (rtr.apply $ .stv i v)[.stv][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_action_change {rtr : Reactor} (h : rtr[.act][i] = some a) : 
    (rtr.apply $ .act i t v)[.act][i] = some (a.schedule t v) := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact ⟨_, ⟨h, rfl⟩⟩ 

theorem apply'_equiv (rtr : Reactor) : (cs : List Change) → rtr.apply' cs ≈ rtr 
  | .nil        => .refl
  | .cons hd tl => Equivalent.trans (rtr.apply hd |>.apply'_equiv tl) (apply_equiv rtr hd)

theorem apply'_preserves_unchanged {rtr : Reactor} {cs : List Change} {cpt : Component.Valued} {i}
    (h : cs.All₂ (¬·.Targets cpt i)) : (rtr.apply' cs)[cpt][i] = rtr[cpt][i] := by
  induction cs generalizing rtr <;> try rfl
  case cons hd tl hi => 
    have ⟨hh, ht⟩ := List.all₂_cons _ _ _ |>.mp h
    exact rtr.apply_preserves_unchanged hh ▸ hi ht 

theorem apply'_disjoint_comm {rtr : Reactor} (h : List.Disjoint cs₁ cs₂) : 
    (rtr.apply' cs₁).apply' cs₂ = (rtr.apply' cs₂).apply' cs₁ :=
  sorry

end Reactor