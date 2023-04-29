import ReactorModel.Execution.Dependency
import Mathlib.Data.Finset.Lattice

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