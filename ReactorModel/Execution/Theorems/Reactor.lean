import ReactorModel.Execution.Reactor
import ReactorModel.Execution.Theorems.Dependency

namespace Reactor

variable [Hierarchical α]

theorem dependencies_subset (rtr : α) (rcn : ID) : dependencies rtr rcn ⊆ rtr[.rcn].ids :=
  fun _ d => d.mem₁

theorem equiv_eq_dependencies {rtr₁ : α} (e : rtr₁ ≈ rtr₂) :
  dependencies rtr₁ = dependencies rtr₂ := by
  ext i j
  exact ⟨.equiv <| .symm e, .equiv e⟩

theorem mem_dependencies_subset {rtr : α} {rcn₁ rcn₂ : ID} (h : rcn₂ ∈ dependencies rtr rcn₁) :
    dependencies rtr rcn₂ ⊆ dependencies rtr rcn₁ :=
  fun _ h' => Dependency.trans h' h

theorem mem_dependencies_ssubset {rtr : α} {rcn₁ rcn₂ : ID}
    (a : Dependency.Acyclic rtr) (h : rcn₂ ∈ dependencies rtr rcn₁) :
    dependencies rtr rcn₂ ⊂ dependencies rtr rcn₁ :=
  ssubset_iff_subset_ne.mpr ⟨mem_dependencies_subset h, (a _ <| ·.symm ▸ h)⟩

end Reactor

namespace Reactor

variable [Proper α]

theorem Refresh.deterministic {rtr : α} (rf₁ : Refresh rtr rtr₁ as) (rf₂ : Refresh rtr rtr₂ as) :
    rtr₁ = rtr₂ := by
  have e := Equivalent.trans (Equivalent.symm rf₁.equiv) rf₂.equiv
  apply ext_obj? e
  intro cpt _ _ _ ho₁ ho₂
  cases cpt
  case stv => injection (rf₁.eq_state ▸ ho₁) ▸ rf₂.eq_state ▸ ho₂
  case act => injection (rf₁.acts     ▸ ho₁) ▸ rf₂.acts     ▸ ho₂
  case inp => injection (rf₁.inputs   ▸ ho₁) ▸ rf₂.inputs   ▸ ho₂
  case out => injection (rf₁.outputs  ▸ ho₁) ▸ rf₂.outputs  ▸ ho₂

variable [Finite α]

theorem refresh_correct (rtr : α) (h : acts.ids = rtr[.act].ids) :
    Refresh rtr (refresh rtr acts) acts where
  equiv := Equivalent.trans set_equiv <| Equivalent.trans set_equiv set_equiv
  eq_state := by
    rw [
      refresh, set_preserves (by simp : .stv ≠ .act), set_preserves (by simp : .stv ≠ .out),
      set_preserves (by simp : .stv ≠ .inp)
    ]
  acts := by
    rw [refresh, set_updated <| h ▸ (Equivalent.ids_eq <| Equivalent.trans set_equiv set_equiv)]
  inputs := by
    rw [
      refresh, set_preserves (by simp : .inp ≠ .act), set_preserves (by simp : .inp ≠ .out),
      set_updated <| Partial.const_ids _ _, Partial.const_eq_map_const
    ]
  outputs := by
    rw [
      refresh, set_preserves (by simp : .out ≠ .act),
      set_updated <| by rw [Equivalent.ids_eq set_equiv, Partial.const_ids _ _],
      Partial.const_eq_map_const
    ]

end Reactor
