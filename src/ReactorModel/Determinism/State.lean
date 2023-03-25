import ReactorModel.Determinism.Dependency

open ReactorType

namespace Execution
namespace State

theorem exec_equiv (s : State) (rcn : ID) : s.rtr ≈ (s.exec rcn).rtr := by
  simp [exec]
  exact Equivalent.symm $ Reactor.apply'_equiv _ _

-- set_option pp.proofs.withType false
theorem exec_indep_input_state_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) : 
    input.state (s.exec rcn₁) rcn₂ = input.state s rcn₂ := by 
  simp [input.state, exec]
  split <;> split <;> try rfl
  case' inl.inr, inr.inl => sorry -- contradiction by "h" hypotheses 
  case inl.inl =>
    sorry
      
theorem exec_indep_input_ports_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) :
    input.ports (s.exec rcn₁) rcn₂ = input.ports s rcn₂ := by 
  sorry
  
theorem exec_indep_input_acts_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) : 
    input.acts (s.exec rcn₁) rcn₂ = input.acts s rcn₂ := by 
  sorry

theorem exec_indep_input_eq {s : State} (hn : rcn₁ ≠ rcn₂) (hi : rcn₁ ≮[s.rtr] rcn₂) : 
    (s.exec rcn₁).input rcn₂ = s.input rcn₂ := by 
  simp [input]
  refine ⟨?ports, ?acts, ?state, rfl⟩
  case state => exact exec_indep_input_state_eq hn hi
  case ports => exact exec_indep_input_ports_eq hn hi
  case acts  => exact exec_indep_input_acts_eq hn hi
    
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