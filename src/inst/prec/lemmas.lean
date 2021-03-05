import inst.prec.basic

variables {υ : Type*} [decidable_eq υ]

namespace «precedence» 

  theorem any_acyc_net_graph_has_wf_prec_graph (η : inst.network.graph υ) (h : η.is_prec_acyclic) :
    ∃ ρ : precedence.graph υ, ρ.is_well_formed_over η :=
    sorry

  lemma wf_prec_graphs_eq_ids (η : inst.network.graph υ) (ρ ρ' : precedence.graph υ) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ.ids = ρ'.ids :=
    begin 
      intros h_wf h_wf',
      have h_i  :  ρ.ids_are_well_formed_over η, from h_wf.left,
      have h_i' : ρ'.ids_are_well_formed_over η, from h_wf'.left,
      rw graph.ids_are_well_formed_over at h_i h_i',
      suffices h : ∀ i, i ∈ ρ.ids ↔ i ∈ ρ'.ids, from finset.ext_iff.mpr h,
      intro i,
      exact iff.trans (h_i i) (iff.symm (h_i' i))
    end

  lemma wf_prec_graphs_eq_data (η : inst.network.graph υ) (ρ ρ' : precedence.graph υ) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ.data = ρ'.data :=
    begin
      intros h_wf h_wf',
      have h_d  :  ρ.data_is_well_formed_over η, from h_wf.right.left,
      have h_d' : ρ'.data_is_well_formed_over η, from h_wf'.right.left,
      rw graph.data_is_well_formed_over at h_d h_d',
      suffices h : ∀ i, ρ.data i = ρ'.data i, from funext h,
      intro i,
      exact eq.trans (h_d i) (eq.symm (h_d' i))
    end

  lemma wf_prec_graphs_eq_edges (η : inst.network.graph υ) (ρ ρ' : precedence.graph υ) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ.edges = ρ'.edges :=
    begin
      intros h_wf h_wf',
      have h_e  :  ρ.edges_are_well_formed_over η, from h_wf.right.right,
      have h_e' : ρ'.edges_are_well_formed_over η, from h_wf'.right.right,
      rw graph.edges_are_well_formed_over at h_e h_e',
      suffices h : ∀ e, e ∈ ρ.edges ↔ e ∈ ρ'.edges, from finset.ext_iff.mpr h,
      intro e,
      exact iff.trans (h_e e) (iff.symm (h_e' e)),
    end

  theorem all_wf_prec_graphs_are_eq (η : inst.network.graph υ) (ρ ρ' : precedence.graph υ) :
    ρ.is_well_formed_over η → ρ'.is_well_formed_over η → ρ = ρ' :=
    begin
      intros h_wf h_wf',
      have h_i : ρ.ids   = ρ'.ids,   from wf_prec_graphs_eq_ids   η ρ ρ' h_wf h_wf',
      have h_d : ρ.data  = ρ'.data,  from wf_prec_graphs_eq_data  η ρ ρ' h_wf h_wf',
      have h_e : ρ.edges = ρ'.edges, from wf_prec_graphs_eq_edges η ρ ρ' h_wf h_wf',
      ext,
        apply finset.ext_iff.mp h_i,
        exact congr_fun h_d x,
        apply finset.ext_iff.mp h_e
    end

  theorem any_acyc_net_graph_has_exactly_one_wf_prec_graph (η : inst.network.graph υ) (h : η.is_prec_acyclic) :
    ∃! ρ : precedence.graph υ, ρ.is_well_formed_over η :=
    begin
      rw exists_unique,
      let ρ := (any_acyc_net_graph_has_wf_prec_graph η h).some,
      have hₚ, from (any_acyc_net_graph_has_wf_prec_graph η h).some_spec,
      apply exists.intro,
        {
          apply and.intro,
            exact hₚ,
            {
              intros m hₘ,
              apply all_wf_prec_graphs_are_eq η m ρ hₘ hₚ
            }
        }
    end

end «precedence»

open precedence.graph

lemma network.graph.equiv_eq_wf_prec_edges {η η' : inst.network.graph υ} {ρ ρ' : precedence.graph υ} :
  η ≈ η' → ρ.is_well_formed_over η → ρ'.is_well_formed_over η' → ρ.edges = ρ'.edges :=
  begin
    intros hₑ_η h_wf h_wf',
    have hₑ, from h_wf.right.right,
    have hₑ', from h_wf'.right.right,
    unfold edges_are_well_formed_over at hₑ hₑ',
    suffices h : ∀ e, e ∈ ρ.edges ↔ e ∈ ρ'.edges, from finset.ext_iff.mpr h,
    intro e,
    replace hₑ := hₑ e,
    replace hₑ' := hₑ' e,
    suffices h : externally_dependent e.src e.dst η ↔ externally_dependent e.src e.dst η', {
      rw h at hₑ,
      exact iff.trans hₑ (iff.symm hₑ')
    },
    simp only [(≈)] at hₑ_η,
    unfold externally_dependent,
    rw hₑ_η.left,
    have hᵣ_eq : ∀ (x : reactor.id), (η.data x).reactions = (η'.data x).reactions, {
      have hᵣ, from hₑ_η.right,
      rw forall_and_distrib at hᵣ,
      exact hᵣ.right.right
    },
    have hₒ : ∀ o, (port_depends_on_reaction o e.src η) ↔ (port_depends_on_reaction o e.src η'), {
      unfold port_depends_on_reaction,
      intro o,
      have h_d : (η.rcn e.src).dₒ = (η'.rcn e.src).dₒ, {
        unfold inst.network.graph.rcn inst.network.graph.rtr,
        rw hᵣ_eq e.src.rtr
      },
      rw h_d
    },
    have hᵢ : ∀ i, (reaction_depends_on_port e.dst i η) ↔ (reaction_depends_on_port e.dst i η'), {
      unfold reaction_depends_on_port,
      intro i,
      have h_d : (η.rcn e.dst).dᵢ = (η'.rcn e.dst).dᵢ, {
        unfold inst.network.graph.rcn inst.network.graph.rtr,
        rw hᵣ_eq e.dst.rtr
      },
      rw h_d
    },
    finish
  end

theorem network.graph.equiv_wf {η η' : inst.network.graph υ} {ρ : precedence.graph υ} :
  η' ≈ η → ρ.is_well_formed_over η → ρ.is_well_formed_over η' :=
  begin
    intros h h_wf,
    unfold precedence.graph.is_well_formed_over at h_wf ⊢,
    simp [(≈)] at h,
    repeat { split },
      {
        unfold ids_are_well_formed_over at h_wf ⊢,
        rw ←h.2.1 at h_wf,
        intro x,
        have h_r, from h.2.2 x.rtr,
        have h_wf', from (h_wf.1 x),
        rw ←h_r.1 at h_wf',
        exact h_wf'
      },
      {
        unfold data_is_well_formed_over at h_wf ⊢,
        intro x,
        sorry
      },
      {
        unfold edges_are_well_formed_over at h_wf ⊢,
        intro x,
        sorry
      } 
  end

theorem network.graph.equiv_prec_acyc_inv {η η' : inst.network.graph υ} :
  η ≈ η' → η.is_prec_acyclic → η'.is_prec_acyclic :=
  begin
    intros hₑ hₚ,
    unfold inst.network.graph.is_prec_acyclic at hₚ ⊢,
    let ρ := classical.subtype_of_exists (precedence.any_acyc_net_graph_has_wf_prec_graph η hₚ),
    intros ρ' h_wf',
    have hₐ, from hₚ ρ ρ.property,
    suffices h : (ρ : precedence.graph υ).edges = ρ'.edges, from digraph.eq_edges_acyclic h hₐ,
    exact network.graph.equiv_eq_wf_prec_edges hₑ ρ.property h_wf',
  end