import ReactorModel.Execution.Reactor
import ReactorModel.Execution.Theorems.Dependency

namespace Reactor

variable [Hierarchical α]

theorem dependencies_subset (rtr : α) (rcn : ID) : dependencies rtr rcn ⊆ rtr[.rcn].ids := 
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

end Reactor

namespace Reactor

variable [Proper α]

theorem Refresh.deterministic {rtr : α} (rf₁ : Refresh rtr rtr₁ as) (rf₂ : Refresh rtr rtr₂ as) : 
    rtr₁ = rtr₂ := by
  have e := Equivalent.trans (Equivalent.symm rf₁.equiv) rf₂.equiv
  apply ext_obj? e
  intro cpt _ _ _ ho₁ ho₂
  cases cpt <;> try cases ‹Component.Writable›
  case stv => injection (rf₁.state   ▸ ho₁) ▸ rf₂.state   ▸ ho₂
  case log => injection (rf₁.logs    ▸ ho₁) ▸ rf₂.logs    ▸ ho₂
  case phy => injection (rf₁.phys    ▸ ho₁) ▸ rf₂.phys    ▸ ho₂
  case inp => injection (rf₁.inputs  ▸ ho₁) ▸ rf₂.inputs  ▸ ho₂
  case out => injection (rf₁.outputs ▸ ho₁) ▸ rf₂.outputs ▸ ho₂

variable [Finite α]

open Equivalent in
theorem refresh_correct (rtr : α) (h : logs.ids = rtr[.log].ids) : 
    Refresh rtr (refresh rtr logs) logs where
  equiv := trans set_equiv $ trans set_equiv $ trans set_equiv set_equiv
  state := by
    rw [
      refresh, set_preserves (by simp : .stv ≠ .log), set_preserves (by simp : .stv ≠ .phy), 
      set_preserves (by simp : .stv ≠ .out), set_preserves (by simp : .stv ≠ .inp)
    ]
  logs := by 
    rw [refresh, set_updated $ h ▸ (ids_eq $ trans set_equiv $ trans set_equiv set_equiv)]
  phys := by 
    rw [
      refresh, set_preserves (by simp : .phy ≠ .log),
      set_updated $ by rw [ids_eq $ Equivalent.trans set_equiv set_equiv, Partial.const_ids _ _], 
      Partial.const_eq_map_const
    ]
  inputs := by 
    rw [
      refresh, set_preserves (by simp : .inp ≠ .log), set_preserves (by simp : .inp ≠ .phy), 
      set_preserves (by simp : .inp ≠ .out), set_updated $ Partial.const_ids _ _, 
      Partial.const_eq_map_const
    ]
  outputs := by 
    rw [
      refresh, set_preserves (by simp : .out ≠ .log), set_preserves (by simp : .out ≠ .phy), 
      set_updated $ by rw [ids_eq set_equiv, Partial.const_ids _ _],
      Partial.const_eq_map_const
    ]

end Reactor