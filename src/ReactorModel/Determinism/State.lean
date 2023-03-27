import ReactorModel.Determinism.Dependency

open Classical ReactorType

namespace Execution
namespace State

theorem exec_equiv (s : State) (rcn : ID) : s.rtr ≈ (s.exec rcn).rtr := by
  simp [exec]
  exact Equivalent.symm $ Reactor.apply'_equiv _ _

-- Note: We could also restate this theorem such that the `m₂` is part of the return value.
theorem exec_objₘ_rcn_eq {s : State} (m₁ : rcn ∈ s.rtr[.rcn]) (m₂ : rcn ∈ (s.exec rcn').rtr[.rcn]) : 
    s.rtr⟦m₁⟧ = (s.exec rcn').rtr⟦m₂⟧ :=
  Equivalent.objₘ_rcn_eq (s.exec_equiv rcn') m₁ |>.choose_spec





theorem port_not_mem_indep_output {s : State} {k i} {rcn₁ rcn₂ : ID}
    (hi : rcn₁ ≮[s.rtr] rcn₂) (m₂ : rcn₂ ∈ s.rtr[.rcn]) (hd : .port k i ∈ s.rtr⟦m₂⟧.deps .in) : 
    (s.output rcn₁).All₂ (¬·.Targets (.prt k) i) := by
  apply List.all₂_iff_forall.mpr
  intro c hc ht
  cases ht
  simp [output] at hc
  split at hc
  case inr => contradiction
  case inl m₁ =>
    have := hi.deps_disjoint m₁ m₂
    have := s.rtr⟦m₁⟧.prtOutDepOnly hc
    exact Ne.irrefl $ Set.disjoint_iff_forall_ne.mp ‹_› ‹_› hd

theorem exec_indep_input_ports_eq {s : State} {rcn₁ rcn₂ : ID} (hi : rcn₁ ≮[s.rtr] rcn₂) (m₁ m₂) :
    input.ports (s.exec rcn₁) rcn₂ m₂ = input.ports s rcn₂ m₁ := by 
  simp [input.ports]
  ext1 k
  rw [←exec_objₘ_rcn_eq m₁ m₂]
  exact Partial.ext_restrict 
    fun _ hd => Reactor.apply'_preserves_unchanged $ port_not_mem_indep_output hi m₁ hd 
  



set_option pp.proofs.withType false
theorem exec_indep_input_state_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) (m₁ m₂) : 
    input.state (s.exec rcn₁) rcn₂ m₂ = input.state s rcn₂ m₁ := by 
  simp [input.state, exec]
  ext1 i
  -- TODO: `s.output rcn₁` does not contain any changes to a state variable in `s.rtr⟦h✝⟧&`.
  --       And hence not to i.
  have H : (s.output rcn₁).All₂ (¬·.Targets .stv i) := sorry 
  have G := s.rtr.apply'_preserves_unchanged H
  sorry

theorem exec_indep_input_acts_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) (m₁ m₂) : 
    input.acts (s.exec rcn₁) rcn₂ m₂ = input.acts s rcn₂ m₁ := by 
  sorry

theorem exec_indep_input_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) : 
    (s.exec rcn₁).input rcn₂ = s.input rcn₂ := by 
  simp [input]
  split <;> split 
  case inr.inr => rfl
  case inr.inl h => 
    have := Equivalent.mem_iff (Equivalent.symm $ Reactor.apply'_equiv _ $ s.output rcn₁) |>.mp h
    contradiction
  case inl.inr h _ =>
    have := Equivalent.mem_iff (Reactor.apply'_equiv _ $ s.output rcn₁) |>.mp h
    contradiction
  case inl.inl m₂ m₁ =>
    simp 
    refine ⟨?ports, ?acts, ?state, rfl⟩
    case state => apply exec_indep_input_state_eq ‹_› ‹_›   
    case ports => apply exec_indep_input_ports_eq ‹_› ‹_›
    case acts  => apply exec_indep_input_acts_eq ‹_› ‹_›
    
    /-
theorem InstStep.indep_rcns_indep_output :
  (e : s ⇓ᵢ s') → (rcn' <[s.rtr]> e.rcn) → (rcn' ≠ e.rcn) → s.output rcn' = s'.rcnOutput rcn' := by
  intro h hi hrne
  have hp := h.exec.preserves_rcns
  cases ho : s.rtr[.rcn][rcn'] <;> cases ho' : s'.rtr[.rcn][rcn']
  case none.none => simp [State.rcnOutput, ho, ho']
  case' none.some, some.none => simp [hp, ho'] at ho
  case some.some => 
    have ⟨⟨p, a, x, t⟩, hj⟩ := State.rcnInput_iff_obj?.mpr ⟨_, ho⟩
    have ⟨⟨p', a', x', t'⟩, hj'⟩ := State.rcnInput_iff_obj?.mpr ⟨_, ho'⟩
    have H1 : p = p' := by 
      simp [s.rcnInput_ports_def hj ho, s'.rcnInput_ports_def hj' ho']
      rw [←hp] at ho'
      have he := Option.some_inj.mp $ ho.symm.trans ho'
      simp [he]
      sorry
    sorry
      
      refine congr_arg₂ _ ?_ rfl
      apply Finmap.restrict_ext
      intro p hp
      have ⟨_, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
      have hd := hi.symm.nonoverlapping_deps hr ho'
      simp [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter] at hd
      have hd := mt (hd p) $ not_not.mpr hp
      simp [Reactor.obj?'_eq_obj?, h.preserves_nondep_ports hr hd]
    have H2 : a = a' := by
      simp [s.rcnInput_actions_def hj ho, s'.rcnInput_actions_def hj' ho']
      rw [←hp] at ho'
      have he := Option.some_inj.mp $ ho.symm.trans ho'
      simp [he]
      apply Finmap.restrict_ext
      intro a ha
      simp [h.preserves_tag]
      apply Finmap.filterMap_congr
      have ⟨_, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
      have hd := hi.symm.nonoverlapping_deps hr ho'
      simp [Finset.eq_empty_iff_forall_not_mem, Finset.mem_inter] at hd
      have hd := mt (hd a) $ not_not.mpr ha
      simp [Reactor.obj?'_eq_obj?, h.preserves_nondep_actions hr hd]
    have H3 : t = t' := by 
      simp [s.rcnInput_time_def hj, s'.rcnInput_time_def hj', h.exec.preserves_tag]
    simp [H1, H2, H3] at hj
    have ⟨r, hr⟩ := Reactor.contains_iff_obj?.mp h.rtr_contains_rcn
    have ⟨_, hc, _⟩ := Reactor.obj?_to_con?_and_cpt? ho
    have ⟨_, hr', _⟩ := Reactor.obj?_to_con?_and_cpt? hr
    cases hi.ne_rtr_or_pure hrne ho hr hc hr'
    case inl he => 
      have ⟨_, hc', _⟩ := Reactor.obj?_to_con?_and_cpt? ho'
      have hs := State.rcnInput_state_def hj hc
      have hs' := State.rcnInput_state_def hj' hc'
      have hq := h.exec.equiv
      have hh := hq.con?_id_eq hc hc'
      have hc := Reactor.con?_to_rtr_obj? hc
      have hc' := Reactor.con?_to_rtr_obj? hc'
      rw [←hh] at hc'
      rw [h.preserves_external_state hr' hc hc' he.symm] at hs
      rw [hs.trans hs'.symm] at hj
      exact State.rcnOutput_congr (hj.trans hj'.symm) hp
    case inr hc =>
      cases hc
      case inl hp' => 
        rw [ho'.symm.trans (h.exec.preserves_rcns ▸ ho)] at ho'
        exact State.rcnOutput_pure_congr hj hj' ho ho' hp'
      case inr hp' => 
        have ⟨_, hco, _⟩ := Reactor.obj?_to_con?_and_cpt? ho
        have ⟨_, hco', _⟩ := Reactor.obj?_to_con?_and_cpt? ho'
        have hs := State.rcnInput_state_def hj hco
        have hs' := State.rcnInput_state_def hj' hco'
        suffices h : x = x' by 
          rw [h] at hj
          exact State.rcnOutput_congr (hj.trans hj'.symm) hp
        rw [hs, hs']
        have he := h.exec.equiv
        exact (he.con?_obj_equiv hco hco').obj?_ext (cpt := .stv) (by
          intro j _
          have h := h.pure_preserves_state (j := j) hr hp'
          have hh := he.con?_id_eq hco hco'
          have hco := Reactor.con?_to_rtr_obj? hco
          have hco' := Reactor.con?_to_rtr_obj? hco'
          rw [←hh] at hco'
          exact he.eq_obj?_nest h hco hco' 
        )
    -/

namespace State
namespace Execution