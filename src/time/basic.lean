import network.basic
import run.basic
import data.rel
import data.finset.basic

@[derive has_le]
def tag := lex ℕ ℕ  

@[derive has_union, derive has_emptyc, derive has_sep (tag × option empty), derive has_mem (tag × option empty)]
def τ := finset (tag × option empty)

structure action_edge := 
  (src : port.id)
  (dst : port.id)

noncomputable instance action_edge_dec_eq : decidable_eq action_edge := classical.dec_eq _

def finset.are_many_to_one (es : finset action_edge) : Prop :=
  ∀ e e' : action_edge, e ∈ es → e' ∈ es →
    e.src = e'.src → e = e'

def finset.have_unique_source_in (es : finset action_edge) (n : network τ) : Prop :=
  ∀ (e : action_edge) (r r' : reaction.id), e ∈ es → 
    (e.src ∈ n.η.dₒ r) → (e.src ∈ n.η.dₒ r') → r = r

def finset.are_functionally_unique_in (es : finset action_edge) (n : network τ) : Prop :=
  ∀ (e e' : action_edge) (r : reaction.id), e ∈ es → e' ∈ es → (e.src ∈ n.η.dₒ r) → (e'.src ∈ n.η.dₒ r) → 
    e.dst = e'.dst → e.src = e'.src

def finset.are_separate_from (es : finset action_edge) (n : network τ) : Prop :=
  ∀ (ae : action_edge) (ne : network.graph.edge), ae ∈ es → ne ∈ n.η → 
    ae.dst ≠ ne.dst ∧ ae.src ≠ ne.src

def finset.are_well_formed_for (es : finset action_edge) (n : network τ) : Prop :=
  es.are_many_to_one ∧ 
  es.have_unique_source_in n ∧ 
  es.are_functionally_unique_in n ∧
  es.are_separate_from n

structure timed_network :=
  (σ : network τ)
  (time : tag)
  (event_queue : list tag)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)

namespace timed_network

  lemma equiv_inst_net_wf_actions (n : timed_network) (σ' : network τ) : 
    σ' ≈ n.σ → n.actions.are_well_formed_for σ' :=
    sorry

  noncomputable def input_action_ports (n : timed_network) : finset port.id :=
    n.actions.image (λ e, e.dst)

  noncomputable def output_action_ports (n : timed_network) : finset port.id :=
    n.actions.image (λ e, e.src)

  noncomputable def priority_of (η : network.graph τ) (e : action_edge) : option ℕ :=
    let rcns := (η.rtr e.src.rtr).rcns_with_dₒ e.src.prt in
    if h : rcns.card = 1 then (finset.card_eq_one.mp h).some else none

end timed_network