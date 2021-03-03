import inst.network.basic
import inst.exec.basic
import data.rel
import data.finset.basic

@[derive has_le]
def tag := lex ℕ ℕ  

@[derive has_union, derive has_emptyc, derive has_sep (tag × option empty), derive has_mem (tag × option empty)]
def tpa := finset (tag × option empty)

structure action_edge := 
  (oap : port.id)
  (iap : port.id)

noncomputable instance action_edge_dec_eq : decidable_eq action_edge := classical.dec_eq _

def finset.are_many_to_one (es : finset action_edge) : Prop :=
  ∀ e e' : action_edge, e ∈ es → e' ∈ es →
    e.oap = e'.oap → e = e'

def finset.are_local (es : finset action_edge) : Prop :=
  ∀ e : action_edge, e ∈ es →
    e.oap.rtr = e.iap.rtr

def finset.have_unique_source_in (es : finset action_edge) (σ : network tpa) : Prop :=
  ∀ (e : action_edge) (r r' : reaction.id), e ∈ es → 
    (e.oap ∈ σ.η.dₒ r) → (e.oap ∈ σ.η.dₒ r') → r = r

def finset.are_functionally_unique_in (es : finset action_edge) (σ : network tpa) : Prop :=
  ∀ (e e' : action_edge) (r : reaction.id), e ∈ es → e' ∈ es → (e.oap ∈ σ.η.dₒ r) → (e'.oap ∈ σ.η.dₒ r) → 
    e.iap = e'.iap → e.oap = e'.oap

def finset.are_separate_from (es : finset action_edge) (σ : network tpa) : Prop :=
  ∀ (ae : action_edge) (ne : network.graph.edge), ae ∈ es → ne ∈ σ.η → 
    ae.iap ≠ ne.dst ∧ ae.oap ≠ ne.src

def finset.are_well_formed_for (es : finset action_edge) (σ : network tpa) : Prop :=
  es.are_many_to_one ∧ 
  es.are_local ∧
  es.have_unique_source_in σ ∧ 
  es.are_functionally_unique_in σ ∧
  es.are_separate_from σ

structure timed_network :=
  (σ : network tpa)
  (time : tag)
  (event_queue : list tag)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)

namespace timed_network

  lemma equiv_inst_net_wf_actions (n : timed_network) (σ' : network tpa) : 
    σ' ≈ n.σ → n.actions.are_well_formed_for σ' :=
    sorry

  noncomputable def input_action_ports (n : timed_network) : finset port.id :=
    n.actions.image (λ e, e.iap)

  noncomputable def output_action_ports (n : timed_network) : finset port.id :=
    n.actions.image (λ e, e.oap)

  noncomputable def priority_of (e : action_edge) (n : network tpa) : option ℕ :=
    let rtr := (n.η.rtr e.oap.rtr) in
    let rcns := rtr.priorities.filter (λ p, p ∈ (rtr.reactions e.oap.prt).dₒ) in
    if h : rcns.card = 1 then (finset.card_eq_one.mp h).some else none

end timed_network