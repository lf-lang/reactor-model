import ReactorModel.Execution.Dependency
import Mathlib.Data.Finset.Lattice

namespace List

def targets (cs : List Change) :=
  { t : Component.Valued × ID | ∃ c ∈ cs, c.Targets t.fst t.snd }

theorem mem_targets_cons (h : t ∈ tl.targets) : t ∈ (hd :: tl).targets := by
  have ⟨c, hm, _⟩ := h 
  exists c, by simp [hm]

theorem target_mem_targets {cs : List Change} (hc : c ∈ cs) (ht : c.target = some t) : 
    t ∈ cs.targets := by
  exists c, hc
  cases c <;> simp [Change.target] at *
  subst ht
  constructor

end List

def Action.schedule (a : Action) (t : Time) (v : Value) : Action :=
  match a.tags.filter (·.time = t) |>.max with
  | ⊥           => a.insert ⟨t, 0⟩ v
  | some ⟨_, m⟩ => a.insert ⟨t, m + 1⟩ v

-- TODO: Split up the following definitions into appropriate namespaces.
namespace ReactorType
namespace Practical

variable [Practical α] 

structure Cleared (rtr₁ rtr₂ : α) : Prop where
  equiv    : rtr₁ ≈ rtr₂
  eq_state : rtr₁[.stv] = rtr₂[.stv]
  eq_acts  : rtr₁[.act] = rtr₂[.act]
  inputs   : rtr₁[.inp].map (fun _ => .absent) = rtr₂[.inp]  
  outputs  : rtr₁[.out].map (fun _ => .absent) = rtr₂[.out]  

theorem Cleared.deterministic {rtr : α} (cl₁ : Cleared rtr rtr₁) (cl₂ : Cleared rtr rtr₂) : 
    rtr₁ = rtr₂ := by
  have e := Equivalent.trans (Equivalent.symm cl₁.equiv) cl₂.equiv
  apply Proper.ext_obj? e
  intro cpt _ _ _ ho₁ ho₂
  cases cpt
  case stv => simp_all [(ho₁ ▸ cl₁.eq_state) ▸ (ho₂ ▸ cl₂.eq_state)] 
  case act => simp_all [(ho₁ ▸ cl₁.eq_acts)  ▸ (ho₂ ▸ cl₂.eq_acts)] 
  case inp => simp_all [(ho₁ ▸ cl₁.inputs)   ▸ (ho₂ ▸ cl₂.inputs)] 
  case out => simp_all [(ho₁ ▸ cl₁.outputs)  ▸ (ho₂ ▸ cl₂.outputs)] 

def apply (rtr : α) : Change → α 
  | .inp i v   => Updatable.update rtr .inp i (fun _ => v)
  | .out i v   => Updatable.update rtr .out i (fun _ => v)
  | .stv i v   => Updatable.update rtr .stv i (fun _ => v)
  | .act i t v => Updatable.update rtr .act i (·.schedule t v)
  | .mut ..    => rtr -- Mutations are currently no-ops.

def apply' (rtr : α) (cs : List Change) : α :=
  cs.foldl apply rtr

def dependencies (rtr : α) (rcn : ID) : Set ID := 
  { rcn' | rcn' <[rtr] rcn }

def dependencies_subset (rtr : α) (rcn : ID) : dependencies rtr rcn ⊆ rtr[.rcn].ids := 
  fun _ d => d.mem₁

theorem equiv_eq_dependencies {rtr₁ : α} (e : rtr₁ ≈ rtr₂) : 
  dependencies rtr₁ = dependencies rtr₂ := by
  ext i j
  exact ⟨.equiv $ .symm e, .equiv e⟩ 

theorem mem_dependencies_subset {rtr : α} {rcn₁ rcn₂ : ID} (h : rcn₂ ∈ dependencies rtr rcn₁) : 
    dependencies rtr rcn₂ ⊆ dependencies rtr rcn₁ :=
  fun _ h' => Dependency.trans h' h

theorem mem_dependencies_ssubset {rtr : α} {rcn₁ rcn₂ : ID} 
    (a : Dependency.Acyclic rtr) (h : rcn₂ ∈ dependencies rtr rcn₁) : 
    dependencies rtr rcn₂ ⊂ dependencies rtr rcn₁ :=
  ssubset_iff_subset_ne.mpr ⟨mem_dependencies_subset h, (a _ $ ·.symm ▸ h)⟩

def scheduledTags (rtr : α) : Set Time.Tag := 
  { g | ∃ i a, (rtr[.act][i] = some a) ∧ (g ∈ a.keys) }

scoped macro "cases_change " change:term : tactic => `(tactic| 
  cases $change:term <;> try cases ‹Change.Normal›; cases ‹Component.Valued›
)

theorem apply_equiv (rtr : α) (c : Change) : (apply rtr c) ≈ rtr := by
  cases_change c <;> first | exact .refl _ | apply Equivalent.symm; apply LawfulUpdatable.equiv

theorem apply_preserves_unchanged {c : Change} (rtr : α) (h : ¬c.Targets cpt i) :
    (apply rtr c)[cpt][i] = rtr[cpt][i] := by
  cases_change c
  all_goals first | exact .refl _ | exact LawfulUpdatable.obj?_preserved (Change.Targets.norm_not h)

variable {rtr : α}

theorem apply_input_change (h : i ∈ rtr[.inp]) : (apply rtr $ .inp i v)[.inp][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_output_change (h : i ∈ rtr[.out]) : (apply rtr $ .out i v)[.out][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_state_change (h : i ∈ rtr[.stv]) : (apply rtr $ .stv i v)[.stv][i] = some v := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact h

theorem apply_action_change (h : rtr[.act][i] = some a) : 
    (apply rtr $ .act i t v)[.act][i] = some (a.schedule t v) := by
  simp [apply, LawfulUpdatable.obj?_updated]
  exact ⟨_, ⟨h, rfl⟩⟩ 

theorem apply_ne_target_comm (ht : c₁.target ≠ c₂.target ∨ c₁.target = none) : 
    apply (apply rtr c₁) c₂ = apply (apply rtr c₂) c₁ := by
  cases_change c₁ <;> cases_change c₂ <;> simp [apply, Change.target] at *
  all_goals exact LawfulUpdatable.update_ne_comm $ by simp_all
    
theorem apply'_equiv (rtr : α) : (cs : List Change) → (apply' rtr cs) ≈ rtr 
  | .nil        => .refl _
  | .cons hd tl => Equivalent.trans (apply'_equiv (apply rtr hd) tl) (apply_equiv rtr hd)

theorem apply'_preserves_unchanged {cs : List Change} {cpt : Component.Valued} {i}
    (h : cs.All₂ (¬·.Targets cpt i)) : (apply' rtr cs)[cpt][i] = rtr[cpt][i] := by
  induction cs generalizing rtr <;> try rfl
  case cons hd tl hi => 
    have ⟨hh, ht⟩ := List.all₂_cons _ _ _ |>.mp h
    exact apply_preserves_unchanged rtr hh ▸ hi ht 

theorem apply'_apply_ne_targets_comm (ht : ∀ {t}, c.target = some t → t ∉ cs.targets) : 
    apply (apply' rtr cs) c = apply' (apply rtr c) cs := by
  induction cs generalizing rtr <;> simp [apply'] at *
  case cons hd tl hi =>
    suffices h : hd.target ≠ c.target ∨ hd.target = none by 
      rw [hi $ fun _ _ h hm => ht _ _ h $ List.mem_targets_cons hm, apply_ne_target_comm h]
    by_contra hc
    push_neg at hc
    have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
    exact ht _ _ (hc.left ▸ h.symm) $ List.target_mem_targets (by simp) h.symm

theorem apply'_disjoint_targets_comm (ht : Disjoint cs₁.targets cs₂.targets) : 
    apply' (apply' rtr cs₁) cs₂ = apply' (apply' rtr cs₂) cs₁ := by
  induction cs₁ generalizing rtr <;> cases cs₂ <;> simp [apply'] at *
  case cons.cons hd₁ tl₁ hd₂ tl₂ hi =>
    have h₁ : Disjoint (List.targets tl₁) (List.targets (hd₂ :: tl₂)) := by
      simp [Set.disjoint_iff_forall_ne]
      intro _ _ hm₁ _ _ hm₂ h₁ h₂
      subst h₁ h₂    
      exact Set.disjoint_left.mp ht (List.mem_targets_cons hm₁) hm₂
    have h₂ : hd₁.target ≠ hd₂.target ∨ hd₁.target = none := by
      by_contra hc
      push_neg at hc
      have ⟨_, h⟩ := Option.ne_none_iff_exists.mp hc.right
      have h₁ := (hd₁ :: tl₁).target_mem_targets (by simp) h.symm
      have h₂ := (hd₂ :: tl₂).target_mem_targets (by simp) (hc.left ▸ h.symm)
      exact Set.disjoint_left.mp ht h₁ h₂
    have h₃ : ∀ {t}, hd₁.target = some t → ¬t ∈ tl₂.targets := by
      intro _ h hm
      have h₁ := (hd₁ :: tl₁).target_mem_targets (by simp) h
      exact Set.disjoint_left.mp ht h₁ $ List.mem_targets_cons hm
    rw [hi h₁, apply_ne_target_comm h₂, ←apply', ←apply', ←apply'_apply_ne_targets_comm h₃]
    rfl
    
end Practical
end ReactorType