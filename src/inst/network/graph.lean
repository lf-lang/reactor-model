import digraph
import inst.network.ids
open reactor
open reactor.ports

-- An edge in a reactor network graph connects reactors' ports.
structure inst.network.graph.edge :=
  (src : port.id)
  (dst : port.id)

-- Reactor network edges are directed.
instance inst.graph.digraph_edge : digraph.edge inst.network.graph.edge reactor.id := 
  { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

-- An instantaneous reactor network graph is a digraph of reactors, identified by reactor-IDs
-- and connected by the edges define above.
def inst.network.graph : Type* := digraph reactor.id (reactor υ) inst.network.graph.edge

namespace inst
namespace network
namespace graph

  variable {υ}

  -- The reactor in a network graph, that is associated with a given reactor ID.
  noncomputable def rtr (η : network.graph υ) (i : reactor.id) : reactor υ := η.data i

  -- The reaction in a network graph, that is associated with a given reaction ID.
  noncomputable def rcn (η : graph υ) (i : reaction.id) : reaction υ :=
    (η.rtr i.rtr).reactions i.rcn

  -- The port in a network graph, that is associated with a given role and port ID.
  noncomputable def port (η : graph υ) (r : ports.role) (i : port.id) : option υ :=
    (η.rtr i.rtr).port r i.prt

  -- The dependencies of a given reaction for a given role, as proper `port.id`s.
  noncomputable def deps (η : graph υ) (i : reaction.id) (r : ports.role) : finset port.id :=
    ((η.rcn i).deps r).image (port.id.mk i.rtr)

  -- A port is part of a reaction's dependencies iff this holds at the reaction level.
  lemma mem_deps_iff_mem_rcn_deps {η : graph υ} {i : reaction.id} {r : ports.role} {p : port.id} :
    p ∈ (η.deps i r) ↔ i.rtr = p.rtr ∧ p.prt ∈ (η.rcn i).deps r :=
    begin
      unfold deps,
      rw finset.mem_image,
      split,  
        {
          intro h,
          obtain ⟨x, hₓ, hₚ⟩ := h,
          simp [←hₚ, hₓ],
        },
        {
          intro h,
          rw h.left,
          existsi p.prt,
          existsi h.right,
          ext ; refl
        }
    end

  -- The edges in a network graph, that are connected to a given output port.
  noncomputable def eₒ (η : graph υ) (p : port.id) : finset graph.edge :=
    η.edges.filter (λ e : graph.edge, e.src = p)

  -- An edge is in `eₒ p` if its source is `p`. 
  lemma mem_eₒ {η : graph υ} (p : port.id) {e : edge} (h : e ∈ η.edges) : e ∈ η.eₒ p ↔ e.src = p :=
    by simp [eₒ, h]

  -- Reactor network graphs' equality is non-constructively decidable.
  noncomputable instance dec_eq : decidable_eq graph.edge := classical.dec_eq _

  -- A reactor is a member of a network graph if the graph contains an ID that maps to it.
  instance rtr_mem : has_mem (reactor υ) (graph υ) := {mem := λ d g, ∃ i, g.data i = d}

  -- Reactor network graphs are equivalent if they are structurally the same and only contain equivalent reactors.
  instance equiv : has_equiv (graph υ) := 
  ⟨λ η η', 
    η.edges = η'.edges ∧ 
    η.ids = η'.ids ∧ 
    ∀ i, (η.rtr i) ≈ (η'.rtr i)
  ⟩

  -- Network graph equivalence is reflexive.
  @[refl] 
  lemma equiv_refl (η : graph υ) : η ≈ η := by simp [(≈)]

  -- Network graph equivalence is symmetric.
  @[symm]
  lemma equiv_symm {η η' : graph υ} (h : η ≈ η') : η' ≈ η :=
    by { simp only [(≈)] at h ⊢, simp [h] }

  -- Network graph equivalence is transitive.
  @[trans]
  lemma equiv_trans {η₁ η₂ η₃ : graph υ} (h₁₂ : η₁ ≈ η₂) (h₂₃ : η₂ ≈ η₃) : η₁ ≈ η₃ :=
    by { simp [(≈)] at ⊢ h₁₂ h₂₃, simp [h₁₂, h₂₃] }

  -- The proposition, that for all input ports (`i`) in `η` the number of edges that end in `i` is ≤ 1.
  def has_unique_port_ins (η : graph υ) : Prop :=
    ∀ e e' : edge, (e ∈ η.edges) → (e' ∈ η.edges) → e ≠ e' → e.dst ≠ e'.dst

  -- The property of having unique port ins only depends on a network graph's edges.
  lemma eq_edges_unique_port_ins {η η' : graph υ} (hₑ : η.edges = η'.edges) (hᵤ : η.has_unique_port_ins) :
    η'.has_unique_port_ins :=
    begin
      unfold has_unique_port_ins,
      intros e e',
      unfold has_unique_port_ins at hᵤ,
      simp [(∈)] at hᵤ ⊢,
      rw ←hₑ,
      apply hᵤ 
    end

  -- Updates the reactor associated with the given reactor ID.
  noncomputable def update_reactor (η : graph υ) (i : reactor.id) (rtr : reactor υ) : graph υ :=
    η.update_data i rtr

  -- Updating a network graph with an equivalent reactor produces an equivalent network graph.
  lemma update_reactor_equiv {η : graph υ} {i : reactor.id} {rtr : reactor υ} (h : η.rtr i ≈ rtr) :
    (η.update_reactor i rtr) ≈ η :=
    begin
      simp only [update_reactor, digraph.update_data, (≈), graph.rtr] at h ⊢,
      repeat { split },
      intro x,
      by_cases hc : x = i,
        { rw hc, simp [function.update_same, h] },
        simp [function.update_noteq hc, h]
    end

  -- Accessing the value of an updated reactor returns exactly the updated value.
  @[simp]
  lemma update_reactor_eq_rtr (η : graph υ) (i : reactor.id) (rtr' : reactor υ) :
    (η.update_reactor i rtr').rtr i = rtr' :=
    by simp [update_reactor, rtr]

  -- Accessing the value of a non-updated reactor returns the same value as before.
  @[simp]
  lemma update_reactor_ne_rtr (η : graph υ) {i i' : reactor.id} (rtr' : reactor υ) (h : i ≠ i') :
    (η.update_reactor i rtr').rtr i' = η.rtr i' :=
    by simp [update_reactor, rtr, digraph.update_data_ne η rtr' (ne.symm h)]

  -- Updating the same reactor twice retains only the last update.
  @[simp]
  lemma update_reactor_same (η : graph υ) (i : reactor.id) (rtr rtr' : reactor υ) :
    (η.update_reactor i rtr).update_reactor i rtr' = η.update_reactor i rtr' :=
    by simp [update_reactor, digraph.update_data]

  -- Updating different reactors is commutative.
  lemma update_reactor_comm (η : graph υ) {i i' : reactor.id} (rtr rtr' : reactor υ) (h : i ≠ i') :
    (η.update_reactor i rtr).update_reactor i' rtr' = (η.update_reactor i' rtr').update_reactor i rtr :=
    by simp [update_reactor, digraph.update_data_comm _ _ _ h]

  -- Relative reactor equality is retained when updating with a relatively equal reactor.
  lemma update_reactor_eq_rel_to {η : graph υ} {i : reaction.id} {rtr' : reactor υ} (h : η.rtr i.rtr =i.rcn= rtr') :
    (η.update_reactor i.rtr rtr').rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      simp only [update_reactor_eq_rtr],
      exact reactor.eq_rel_to_symm h
    end

  -- Updates the port associated with the given role and port ID.
  noncomputable def update_port (η : graph υ) (r : ports.role) (p : port.id) (v : option υ) : graph υ :=
    η.update_reactor p.rtr ((η.rtr p.rtr).update r p.prt v)

  -- Updating a port on one side of a reactor does not change the ports on the other side.
  @[simp]
  lemma update_port_opposite_eq (η : graph υ) (r : ports.role) (p : port.id) (v : option υ) :
    (η.update_port r p v).port r.opposite = η.port r.opposite :=
    begin
      unfold update_port,
      ext1,
      cases r ; {
        by_cases hc : x.rtr = p.rtr,
          all_goals { simp only [ports.role.opposite, update, port, reactor.port] },
          simp only [hc, update_reactor_eq_rtr],
          rw update_reactor_ne_rtr η _ (ne.symm hc),
      }
    end

  -- Updating different ports is commutative.
  lemma update_port_comm (η : graph υ) (r : ports.role) {p p' : port.id} (v v' : option υ) (h : p ≠ p') :
    (η.update_port r p v).update_port r p' v' = (η.update_port r p' v').update_port r p v :=
    begin
      unfold update_port,
      by_cases hc : p.rtr = p'.rtr,
        {
          rw hc,
          repeat { rw update_reactor_same },
          unfold update_reactor rtr,
          apply congr,
          refl,
          repeat { rw digraph.update_data_same },
          rw reactor.update_comm,
          cases p,
          cases p',
          intro h',
          apply_assumption,
          ext,
          assumption',
        },
        rw [update_reactor_comm _ _ _ hc, update_reactor_ne_rtr _ _ hc, update_reactor_ne_rtr _ _ (ne.symm hc)],
    end

  -- Updating a port in a network graph produces an equivalent network graph.
  lemma update_port_equiv (η : graph υ) (r : ports.role) (p : port.id) (v : option υ) :
    η ≈ (η.update_port r p v) :=
    begin
      unfold update_port,
      have h, from reactor.update_equiv (η.rtr p.rtr) r p.prt v,
      symmetry,
      exact update_reactor_equiv (reactor.equiv_symm h)
    end

  -- Updating an input port that is not a dependency of a given reaction produces an equal reactor relative to that reaction.
  lemma update_input_eq_rel_to {η : graph υ} {i : reaction.id} {p : ℕ} (v : option υ) (h : p ∉ (η.rcn i).dᵢ) :
    (η.update_port role.input ⟨i.rtr, p⟩ v).rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      simp only [update_port, update_reactor, rtr, digraph.update_data_same, rcn] at h ⊢,
      exact reactor.eq_rel_to_symm (reactor.eq_rel_to.single (refl _) h)
    end 

  -- Runs a given reaction within the context of its reactor. 
  -- That is, without propagating any outputs.
  noncomputable def run_local (η : graph υ) (i : reaction.id) : graph υ :=
    η.update_reactor i.rtr ((η.rtr i.rtr).run i.rcn)

  -- Running a reaction locally does not change any other reactors in the network graph.
  @[simp]
  lemma run_local_is_local (η : graph υ) {iₙ : reaction.id} {iᵣ : reactor.id} (h : iₙ.rtr ≠ iᵣ) :
    (η.run_local iₙ).rtr iᵣ = η.rtr iᵣ :=
    by simp [run_local, update_reactor_ne_rtr, h]

  -- Running a reaction locally produces an equivalent network graph.
  lemma run_local_equiv (η : graph υ) (i : reaction.id) : η.run_local i ≈ η :=
    begin
      unfold run_local,
      have h, from reactor.run_equiv (η.rtr i.rtr) i.rcn,
      exact update_reactor_equiv (reactor.equiv_symm h)
    end

  -- Running a reaction locally produces retains relative equality for all other reactors.
  lemma run_local_eq_rel_to (η : graph υ) {i i' : reaction.id} (h : i.rtr ≠ i'.rtr) :
    (η.run_local i).rtr i'.rtr =i'.rcn= η.rtr i'.rtr :=
    by { rw run_local_is_local η h, apply eq_rel_to_refl }

  -- Running two reactions that live in different reactors locally is commutative.
  lemma run_local_comm (η : graph υ) {i i' : reaction.id} (h : i.rtr ≠ i'.rtr) :
    (η.run_local i).run_local i' = (η.run_local i').run_local i :=
    by simp [run_local, update_reactor_ne_rtr _ _ h, update_reactor_ne_rtr _ _ (ne.symm h), update_reactor_comm _ _ _ h]

  -- Output ports which are not in the output dependencies of a reaction, are not affected by running that reaction.
  @[simp]
  lemma run_local_output_eq {η : graph υ} {i : reaction.id} {p : port.id} (h : p ∉ η.deps i role.output) :
    (η.run_local i).port role.output p = η.port role.output p :=
    begin
      unfold run_local,
      unfold port,
      unfold update_reactor rtr,
      by_cases hc : i.rtr = p.rtr,
        {
          rw [hc, digraph.update_data_same],
          rw [mem_deps_iff_mem_rcn_deps, not_and, rcn, rtr, hc] at h,
          exact reactor.run_out_not_dₒ_eq (h (refl _))
        },
        rw digraph.update_data_ne _ _ (ne.symm hc)
    end

  -- Running a reaction locally, and updating an input port is commutative, if the input port is not part of the
  -- reaction's input dependencies.
  lemma run_local_update_input_comm {η : graph υ} {i : reaction.id} {p : port.id} (v : option υ) (h : p ∉ η.deps i role.input) :
    (η.run_local i).update_port role.input p v = (η.update_port role.input p v).run_local i :=
    begin
      by_cases hc : p.rtr = i.rtr,
        {
          unfold update_port run_local,
          rw hc,
          repeat { rw [update_reactor_same, update_reactor_eq_rtr] },
          rw run_update_input_comm,
          rw [mem_deps_iff_mem_rcn_deps, not_and] at h,
          exact h (eq.symm hc)
        },
        {
          unfold update_port run_local,
          rw update_reactor_ne_rtr _ _ hc,
          rw update_reactor_ne_rtr _ _ (ne.symm hc),
          exact update_reactor_comm _ _ _ (ne.symm hc)
        }
    end

  -- Returns the index-diff of the ports (of a given role) of the same reactor in two different network graphs.
  noncomputable def index_diff (η η' : graph υ) (i : reactor.id) (r : ports.role) : finset port.id :=
    (((η.rtr i).prts r).index_diff ((η'.rtr i).prts r)).image (port.id.mk i)

  -- Running a reaction in two network graphs that have relatively equal reactors for that reaction, produces the
  -- same output index-diff for those reactors.
  lemma run_local_index_diff_eq_rel_to {η η' : graph υ} {i : reaction.id} (h : η.rtr i.rtr =i.rcn= η'.rtr i.rtr) :
    (η.run_local i).index_diff η i.rtr role.output = (η'.run_local i).index_diff η' i.rtr role.output :=
    by simp [index_diff, prts, run_local, eq_rel_to_eq_output h, eq_rel_to_eq_output (run_eq_rel_to h)]

end graph
end network
end inst