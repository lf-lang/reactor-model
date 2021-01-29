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

def finset.are_output_unique (es : finset action_edge) : Prop :=
  ∀ e e' : action_edge, e ∈ es → e' ∈ es → 
    e.src = e'.src → e = e'

def finset.are_input_unique_for (es : finset action_edge) (n : network τ) : Prop :=
  ∀ (e : action_edge) (r r' : reaction.id), e ∈ es → 
    (e.src ∈ n.η.dₒ r) ∧ (e.src ∈ n.η.dₒ r') → r = r

def finset.are_separate_from (es : finset action_edge) (n : network τ) : Prop :=
  ∀ (e : action_edge) (e' : network.graph.edge), e ∈ es → e' ∈ n.η → 
    e.dst ≠ e'.src ∧ e.src ≠ e'.dst

def finset.are_well_formed_for (es : finset action_edge) (n : network τ) : Prop :=
  es.are_output_unique ∧ 
  es.are_input_unique_for n ∧ 
  es.are_separate_from n

structure timed_network :=
  (σ : network τ)
  (time : tag)
  (event_queue : list tag)
  (actions : finset action_edge)
  (well_formed : actions.are_well_formed_for σ)

namespace timed_network

  noncomputable def input_action_ports (n : timed_network) : finset port.id :=
    n.actions.image (λ e, e.dst)

  noncomputable def output_action_ports (n : timed_network) : finset port.id :=
    n.actions.image (λ e, e.src)

  noncomputable def priority_of (η : network.graph τ) (e : action_edge) : option ℕ :=
    let rcns := (η.rtr e.src.rtr).rcns_with_dₒ e.src.prt in
    if h : rcns.card = 1 then (finset.card_eq_one.mp h).some else none

  def priority_pred (η : network.graph τ) (e e' : action_edge) : Prop :=
    sorry

  instance {η : network.graph τ} : is_total action_edge (priority_pred η) := sorry
  instance {η : network.graph τ} : is_antisymm action_edge (priority_pred η) := sorry
  instance {η : network.graph τ} : is_trans action_edge (priority_pred η) := sorry
  instance {η : network.graph τ} : decidable_rel (priority_pred η) := sorry

  def merge_τs (o o' : option τ) (cutoff : tag) : τ :=
    let m := o.elim ∅ id, m' := o.elim ∅ id in
    let m'' := m'.filter (λ tv', ∀ tv : (tag × option empty), tv ∈ m → tv.1 ≠ tv'.1) in
    (m ∪ m'').filter (λ tv, cutoff ≤ tv.1)

  -- In this context "propagating" means consuming the source value, i.e. setting it to `none` once used.
  noncomputable def propagate_τ (cutoff : tag) (η : network.graph τ) (e : action_edge) : network.graph τ :=
    (η.update_input e.dst (merge_τs (η.input e.dst) (η.output e.src) cutoff))
      .update_output e.src none

  noncomputable def gather_input_action_port (cutoff : tag) (as : finset action_edge) (η : network.graph τ) (p : port.id) : network.graph τ :=
    ((as
      .filter (λ a : action_edge, a.dst = p))
      .sort (priority_pred η))
      .foldl (propagate_τ cutoff) η

  private noncomputable def at_tag_aux (n : timed_network) (t : tag) : network.graph τ :=
    n.input_action_ports.val.to_list.foldl (gather_input_action_port t n.actions) n.σ.η 

  lemma at_tag_aux_unique_ins {n : timed_network} (t : tag) :
    n.σ.η.has_unique_port_ins → (at_tag_aux n t).has_unique_port_ins :=
    sorry

  lemma at_tag_aux_prec_acyclic {n : timed_network} (t : tag) :
    n.σ.η.is_prec_acyclic → (at_tag_aux n t).is_prec_acyclic :=
    sorry

  noncomputable def at_tag (n : timed_network) (t : tag) : network τ :=
    {
      η := at_tag_aux n t,
      unique_ins := at_tag_aux_unique_ins t n.σ.unique_ins,
      prec_acyclic := at_tag_aux_prec_acyclic t n.σ.prec_acyclic
    }

  noncomputable def ports_for_actions (actions : finset action_edge) : finset port.id × finset port.id :=
    let ps := actions.image (λ e : action_edge, (e.dst, e.src)) in
    (ps.image prod.fst, ps.image prod.snd)

  noncomputable def run_inst (σ : network τ) (fₚ : prec_func τ) (tₚ : topo_func τ) (actions : finset action_edge) : network τ :=
    let ⟨i, o⟩ := ports_for_actions actions in (σ.run fₚ tₚ).clear_ports_excluding i o

  noncomputable def events_for (σ : network τ) (aops : finset port.id) : finset tag :=
    aops.bind (λ p, let o := σ.η.output p in o.elim ∅ (finset.image prod.fst))

  noncomputable def run_aux (n : timed_network) (fₚ : prec_func τ) (tₚ : topo_func τ) : list tag → timed_network
    | [] := n
    | (hd :: tl) := 
      let σ' := run_inst n.σ fₚ tₚ n.actions in
      {
        σ := σ',
        time := hd,
        event_queue := (tl ++ (events_for σ' n.output_action_ports).val.to_list).merge_sort (≤),
        actions := n.actions,
        well_formed := sorry
      }

  noncomputable def run (n : timed_network) (fₚ : prec_func τ) (tₚ : topo_func τ) : timed_network :=
    run_aux n fₚ tₚ n.event_queue

end timed_network