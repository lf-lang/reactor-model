import ReactorModel.Determinism.Dependency

open Classical ReactorType

namespace Execution

theorem InstStep.rcn_not_mem_progress (e : s₁ ⇓ᵢ s₂) : e.rcn.id ∉ s₁.progress := 
  sorry -- e.allows.unprocessed

theorem InstStep.preserves_tag (e : s₁ ⇓ᵢ s₂) : s₁.tag = s₂.tag := 
  sorry -- e.exec.preserves_tag
  
theorem InstStep.mem_progress_iff :
  (e : s₁ ⇓ᵢ s₂) → (rcn' ∈ s₂.progress ↔ rcn' = e.rcn ∨ rcn' ∈ s₁.progress) := by
  intro h
  constructor
  case mp =>
    intro ho
    by_cases hc : rcn' = h.rcn
    case pos => exact .inl hc
    case neg => sorry
      -- rw [State.progress, h.exec.ctx_adds_rcn, ←rcn] at ho
      -- simp [Context.mem_record_progress_iff _ _ _ |>.mp ho]
  case mpr =>
    intro ho
    by_cases hc : rcn' = h.rcn
    case pos =>
      simp [hc]
      sorry
      -- exact Context.mem_record_progress_iff _ _ _ |>.mpr (.inl rfl)
    case neg =>
      sorry
      -- simp [State.progress, h.exec.ctx_adds_rcn, Context.mem_record_progress_iff _ _ _ |>.mpr (.inr $ ho.resolve_left hc)]

-- Corollary of `InstStep.mem_progress_iff`.
theorem InstStep.not_mem_progress :
  (e : s₁ ⇓ᵢ s₂) → (rcn' ≠ e.rcn) → rcn'.id ∉ s₁.progress → rcn'.id ∉ s₂.progress := 
  sorry -- λ h hn hm => (mt h.mem_progress.mp) $ not_or.mpr ⟨hn, hm⟩

-- Corollary of `InstStep.mem_progress`.
theorem InstStep.monotonic_progress : (s₁ ⇓ᵢ s₂) → rcn' ∈ s₁.progress → rcn' ∈ s₂.progress := 
  sorry -- (·.mem_progress_iff.mpr $ .inr ·)

-- Corollary of `InstStep.mem_progress`.
theorem InstStep.rcn_mem_progress : (e : s₁ ⇓ᵢ s₂) → e.rcn.id ∈ s₂.progress := 
  (·.mem_progress_iff.mpr $ .inl rfl)

theorem identified_changes_equiv_changes {cs : List Change} {o : List (Identified Change)} : 
  (cs.map ({ id := i, obj := ·}) = o) → (o.map (·.obj) = cs) := by
  intro h
  induction cs generalizing o
  case nil => simp_all
  case cons hd tl hi =>
    cases o <;> simp [List.map_cons] at h ⊢
    case cons hd' tl' =>
      specialize hi h.right
      simp [h.left.symm, hi]
      
-- If a port is not in the output-dependencies of a given reaction,
-- then any instantaneous step of the reaction will keep that port
-- unchanged.
theorem InstStep.preserves_nondep_ports : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr[.rcn][e.rcn] = some r) → (.port k p ∉ r.deps .out) → (s₁.rtr[.prt k][p] = s₂.rtr[.prt k][p])
  := sorry
  /-
  | skipReaction ..,         _,  _ => rfl
  | execReaction _ _ ho hs, hr, hd => 
    hs.preserves_unchanged_ports (
      s₁.rcnOutput_port_dep_only · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hr hd
    )
  -/

theorem InstStep.preserves_nondep_actions : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr[.rcn][e.rcn] = some r) → (.action a ∉ r.deps .out) → (s₁.rtr[.act][a] = s₂.rtr[.act][a])
  := sorry
  /-
  | skipReaction ..,        _,  _ => rfl
  | execReaction _ _ ho hs, hr, hd => 
    hs.preserves_unchanged_actions (
      s₁.rcnOutput_action_dep_only · · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hr hd
    )
  -/

theorem InstStep.pure_preserves_state {j : ID} : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr[.rcn][e.rcn] = some r) → (r.Pure) → (s₁.rtr[.stv][j] = s₂.rtr[.stv][j])
  := sorry
  /-
  | skipReaction ..,    _,  _ => rfl
  | execReaction _ _ ho hs, hr, hp =>
    hs.preserves_unchanged_state (
      s₁.rcnOutput_pure · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hr hp
    )
  -/

-- Note: We can't express the result as `∀ x, c₁.obj? .stv x = c₂.obj? .stv x`,
--       as `c₁`/`c₂` might contain `c` as a (transitively) nested reactor. 
theorem InstStep.preserves_external_state : 
  (e : s₁ ⇓ᵢ s₂) → (s₁.rtr[.rcn][e.rcn]& = some c) → 
  (s₁.rtr[.rtr][j] = some c₁) → (s₂.rtr[.rtr][j] = some c₂) → (c.id ≠ j) →
  (c₁.state = c₂.state)
  := sorry
  /-
  | skipReaction ..,        _,  _,   _,   _ => by simp_all
  | execReaction _ _ ho hs, hc, hc₁, hc₂, hi => by
    apply hs.preserves_Equiv.nest' hc₁ hc₂ |>.obj?_ext (cpt := .stv)
    intro x hx
    have hm := Reactor.local_mem_exclusive hc₁ (Reactor.con?_to_rtr_obj? hc) hi.symm hx
    have hu := hs.preserves_unchanged_state (
      s₁.rcnOutput_state_local · (by
        simp [State.rcnOutput'] at ho
        have ⟨_, hcs, ho⟩ := ho
        simp [rcn, hcs, identified_changes_equiv_changes ho]
      ) hc hm
    )
    exact hs.preserves_Equiv.eq_obj?_nest hu hc₁ hc₂
  -/
 
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

namespace InstStep

theorem Skip.equiv : (s₁ ⇓ₛ s₂) → s₁.rtr ≈ s₂.rtr
  | mk .. => .refl

theorem Skip.progress_eq : (e : s₁ ⇓ₛ s₂) → s₂.progress = s₁.progress.insert e.rcn.id
  | mk .. => rfl

theorem Skip.progress_mono (e : s₁ ⇓ₛ s₂) : s₁.progress ⊆ s₂.progress := by
  simp [e.progress_eq]
  apply Set.subset_insert

theorem Skip.triggers_iff (e : s₁ ⇓ₛ s₂) : (s₁.Triggers ⟨i, h₁⟩) ↔ (s₂.Triggers ⟨i, h₂⟩) := by 
  cases e
  case mk rcn _ _ =>
    constructor
    all_goals
      intro h
      exact h.progress_agnostic (s₁.record_preserves_rtr rcn) (s₁.record_preserves_tag rcn)

theorem Skip.mem_progress_iff (e : s₁ ⇓ₛ s₂) : 
    (rcn' ∈ s₂.progress) ↔ (rcn' = e.rcn ∨ rcn' ∈ s₁.progress) := by
  sorry

theorem Skip.preserves_allows_indep (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ₛ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    s₁.Allows e₂.rcn where
  unprocessed := Set.not_mem_subset e₁.progress_mono $ e₂.allows_rcn.unprocessed
  deps := by
    intro i hi
    have h' := Reactor.equiv_eq_dependencies e₁.equiv |>.symm ▸ e₂.allows_rcn.deps
    refine e₁.mem_progress_iff.mp (h' hi) |>.resolve_left ?_
    intro hc; subst hc; contradiction

set_option pp.proofs.withType false
theorem Skip.swap_indep_skip (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ₛ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    ∃ (s₂' : _) (f₁ : s₁ ⇓ₛ s₂') (f₂ : s₂' ⇓ₛ s₃), (f₁.rcn.id = e₂.rcn) ∧ (f₂.rcn.id = e₁.rcn) := by 
  have ha := e₁.preserves_allows_indep e₂ h
  have ht := e₁.triggers_iff (h₁ := sorry) |>.not.mpr e₂.not_triggers
  have e₁' := Skip.mk ha ht
  simp at e₁'
  exists _, e₁'
  sorry -- TODO: This is super annoying. Is there a better way to approach this?
        --       Do we need more preservation theorems for `Allows` and `Triggers` first?

theorem Skip.swap_indep_exec (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ₑ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    ∃ (s₂' : _) (f₁ : s₁ ⇓ₑ s₂') (f₂ : s₂' ⇓ₛ s₃), (f₁.rcn.id = e₂.rcn) ∧ (f₂.rcn.id = e₁.rcn) := by 
  sorry

theorem Skip.swap_indep (e₁ : s₁ ⇓ₛ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) : 
    ∃ (s₂' : _) (f₁ : s₁ ⇓ᵢ s₂') (f₂ : s₂' ⇓ₛ s₃), (f₁.rcn.id = e₂.rcn) ∧ (f₂.rcn.id = e₁.rcn) := by 
  cases e₂
  case skip e₂ =>
    have ⟨_, e₁', e₂', _⟩ := e₁.swap_indep_skip e₂ h
    exists _, skip e₁', e₂'
  case exec e₂ =>
    have ⟨_, e₁', e₂', _⟩ := e₁.swap_indep_exec e₂ h
    exists _, exec e₁', e₂'

theorem Exec.equiv : (s₁ ⇓ₑ s₂) → s₁.rtr ≈ s₂.rtr
  | mk .. => by simp [State.record_preserves_rtr, Equivalent.symm $ s₁.exec_equiv _]

theorem Exec.progress_eq : (e : s₁ ⇓ₑ s₂) → s₂.progress = s₁.progress.insert e.rcn.id
  | mk .. => rfl

theorem not_Closed (e : s₁ ⇓ᵢ s₂) : ¬s₁.Closed := by
  intro c
  have h := c ▸ e.allows_rcn.unprocessed
  simp [Partial.mem_ids_iff] at h 
  have := e.rcn.obj?_id_eq_obj ▸ h e.rcn.obj
  contradiction 

theorem equiv : (s₁ ⇓ᵢ s₂) → s₁.rtr ≈ s₂.rtr
  | skip e | exec e => e.equiv

theorem deterministic (e₁ : s ⇓ᵢ s₁) (e₂ : s ⇓ᵢ s₂) (h : e₁.rcn = e₂.rcn) : s₁ = s₂ := by
  cases e₁ <;> cases e₂
  all_goals 
    case _ e₁ e₂ => 
      cases e₁; cases e₂
      simp [rcn] at h
      subst h
      first | rfl | contradiction

theorem acyclic (e : s₁ ⇓ᵢ s₂) : e.rcn ≮[s₁.rtr] e.rcn :=
  e.allows_rcn.acyclic

theorem progress_eq : (e : s₁ ⇓ᵢ s₂) → s₂.progress = s₁.progress.insert e.rcn.id
  | skip e | exec e => e.progress_eq  

/-
By cases on e₁ and e₂:
(1) skip.skip:
    then both didn't trigger and nothing about the reactors changed, so it is easy to show that
    switching the order preserves non-triggering.

(2)&(3) exec.skip and skip.exec:
        using `preserves_triggers` it should be easy

(4) exec.exec: 
    reduces to a theorem on State.exec?
-/
theorem prepend_indep (e₁ : s₁ ⇓ᵢ s₂) (e₂ : s₂ ⇓ᵢ s₃) (h : e₁.rcn ≮[s₁.rtr] e₂.rcn) :
    ∃ (s₂' : _) (e₁' : s₁ ⇓ᵢ s₂') (e₂' : s₂' ⇓ᵢ s₃), e₁'.rcn.id = e₂.rcn ∧ e₂'.rcn.id = e₁.rcn := by
  cases e₁ 
  case skip e₁ => 
    have ⟨_, e₁', e₂', _⟩ := e₁.swap_indep e₂ h
    exists _, e₁', skip e₂'
  case exec e₁ =>
    sorry 

end InstStep 
end Execution