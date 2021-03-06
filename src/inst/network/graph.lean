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
    η.edges.filter (λ e, (e : graph.edge).src = p)

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
    by simp [update_reactor, rtr, digraph.update_data_noteq η rtr' (ne.symm h)]

  -- Updating the same reactor twice retains only the last update.
  @[simp]
  lemma update_reactor_same (η : graph υ) (i : reactor.id) (rtr rtr' : reactor υ) :
    (η.update_reactor i rtr).update_reactor i rtr' = η.update_reactor i rtr' :=
    by simp [update_reactor, digraph.update_data]

  -- Relative reactor equality is retained when updating with a relatively equal reactor.
  lemma update_reactor_eq_rel_to {η : graph υ} {i : reaction.id} {rtr' : reactor υ} (h : η.rtr i.rtr =i.rcn= rtr') :
    (η.update_reactor i.rtr rtr').rtr i.rtr =i.rcn= η.rtr i.rtr :=
    begin
      simp only [update_reactor_eq_rtr],
      exact reactor.eq_rel_to_symm h
    end

  -- Updates the port associated with the given role and port ID.
  noncomputable def update_port (η : graph υ) (r : reactor.ports.role) (p : port.id) (v : option υ) : graph υ :=
    η.update_reactor p.rtr ((η.rtr p.rtr).update r p.prt v)

  -- Updating a port in a network graph produces an equivalent network graph.
  lemma update_port_equiv (η : graph υ) (r : ports.role) (p : port.id) (v : option υ) :
    η ≈ (η.update_port r p v) :=
    begin
      unfold update_port,
      have h, from reactor.update_equiv (η.rtr p.rtr) r p.prt v,
      symmetry,
      exact update_reactor_equiv (reactor.equiv_symm h)
    end

  -- Updating a port that is not a dependency of a given reaction produces an equal reactor relative to that reaction.
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

  -- Running a reaction locally produces an equivalent network graph.
  lemma run_local_equiv (η : graph υ) (i : reaction.id) : η.run_local i ≈ η :=
    begin
      unfold run_local,
      have h, from reactor.run_equiv (η.rtr i.rtr) i.rcn,
      exact update_reactor_equiv (reactor.equiv_symm h)
    end

  -- It makes no difference whether we first run a reaction, and then update its reactor's input 
  -- (only ports which the reaction doesn't depend on), or if we do it the other way around.
  lemma run_local_update_inputs_comm {η : graph υ} {i : reaction.id} {rtr' : reactor υ} (h : η.rtr i.rtr =i.rcn= rtr') :
    (η.run_local i).update_reactor i.rtr {reactor . input := rtr'.input, .. (η.run_local i).rtr i.rtr} = 
    (η.update_reactor i.rtr rtr').run_local i :=
    begin
      have hq₁, from run_local_equiv η i,
      have hq₂, from update_reactor_equiv (reactor.eq_rel_to_equiv h),
      have hq, from graph.equiv_trans hq₁ (graph.equiv_symm hq₂),
      simp only [(≈)] at hq,
      obtain ⟨hₑ, hᵢ, hᵣ⟩ := hq,
      ext1,
        {
          cases ((η.update_reactor i.rtr rtr').run_local i).ids,
          exact hᵢ,
        },
        {
          unfold run_local,
          have h', from reactor.eq_rel_to_symm (update_reactor_eq_rel_to h),
          rw ←(reactor.run_update_inputs_comm h'),
          simp,
        },
        {
          cases ((η.update_reactor i.rtr rtr').run_local i).edges,
          exact hₑ,
        }
    end

end graph
end network
end inst