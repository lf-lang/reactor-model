import ReactorModel.Execution.Dependency
import Mathlib.Data.Finset.Lattice

noncomputable section
open Classical

-- TODO: Split up the following definitions into appropriate namespaces.
namespace ReactorType
namespace Practical

variable [Practical α] 

structure Refresh (rtr₁ rtr₂ : α) (acts : ID ⇀ Value) : Prop where
  equiv    : rtr₁ ≈ rtr₂
  eq_state : rtr₂[.stv] = rtr₁[.stv]
  acts     : rtr₂[.act] = acts
  inputs   : rtr₂[.inp] = rtr₁[.inp].map fun _ => .absent
  outputs  : rtr₂[.out] = rtr₁[.out].map fun _ => .absent

theorem Refresh.deterministic {rtr : α} (rf₁ : Refresh rtr rtr₁ as) (rf₂ : Refresh rtr rtr₂ as) : 
    rtr₁ = rtr₂ := by
  have e := Equivalent.trans (Equivalent.symm rf₁.equiv) rf₂.equiv
  apply Proper.ext_obj? e
  intro cpt _ _ _ ho₁ ho₂
  cases cpt
  case stv => injection (rf₁.eq_state ▸ ho₁) ▸ rf₂.eq_state ▸ ho₂
  case act => injection (rf₁.acts     ▸ ho₁) ▸ rf₂.acts     ▸ ho₂
  case inp => injection (rf₁.inputs   ▸ ho₁) ▸ rf₂.inputs   ▸ ho₂
  case out => injection (rf₁.outputs  ▸ ho₁) ▸ rf₂.outputs  ▸ ho₂

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

end Practical
end ReactorType