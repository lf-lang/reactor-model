import digraph
import inst.reactor
import inst.network.ids
open reactor
open reactor.ports

-- An edge in a reactor network graph connects reactors' ports.
structure network.graph.edge :=
  (src : port.id)
  (dst : port.id)

-- Reactor network edges are directed.
instance graph.digraph_edge : digraph.edge network.graph.edge reactor.id := 
  { src := (λ e, e.src.rtr), dst := (λ e, e.dst.rtr) }

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

-- A reactor network graph is a digraph of reactors, identified by reactor-IDs and connected
-- by the edges define above.
def network.graph : Type* := digraph reactor.id (reactor υ) network.graph.edge

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

  -- The output dependencies of a given reaction, as proper `port.id`s.
  noncomputable def dₒ (η : graph υ) (i : reaction.id) : finset port.id :=
    (η.rcn i).dₒ.image (λ p, {port.id . rtr := i.rtr, prt := p})

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

  -- Updates the port associated with the given role and port ID.
  noncomputable def update_port (η : graph υ) (r : reactor.ports.role) (p : port.id) (v : option υ) : graph υ :=
    η.update_reactor p.rtr ((η.rtr p.rtr).update r p.prt v)

  -- Updating a port in a network graph produces an equivalent network graph.
  lemma update_port_equiv (η : graph υ) (r : ports.role) (p : port.id) (v : option υ) :
    (η.update_port r p v) ≈ η :=
    begin
      unfold update_port,
      have h, from reactor.update_equiv (η.rtr p.rtr) r p.prt v,
      exact update_reactor_equiv (reactor.equiv_symm h)
    end









  noncomputable def run_locally (η : graph υ) (i : reaction.id) : graph υ :=
    η.update_reactor i.rtr ((η.rtr i.rtr).run i.rcn)

  lemma run_locally_equiv (η : graph υ) (i : reaction.id) : η.run_locally i ≈ η :=
    sorry

  lemma update_reactor_eq_rel_to {η : graph υ} {i : reaction.id} {rtr' : reactor υ} (h : η.rtr i.rtr =i.rcn= rtr') :
    (η.update_reactor i.rtr rtr').rtr i.rtr =i.rcn= η.rtr i.rtr :=
    sorry

  @[simp]
  lemma update_reactor_eq_rtr (η : graph υ) (i : reactor.id) (rtr' : reactor υ) :
    (η.update_reactor i rtr').rtr i = rtr' :=
    sorry

  @[simp]
  lemma update_reactor_same (η : graph υ) (i : reactor.id) (rtr rtr' : reactor υ) :
    (η.update_reactor i rtr).update_reactor i rtr' = η.update_reactor i rtr' :=
    sorry


  -- It makes no difference whether we first run a reaction, and then update its reactor's input 
  -- (only ports which the reaction doesn't depend on), or if we do it the other way around.
  lemma run_update_input_comm {η : graph υ} {i : reaction.id} {rtr' : reactor υ} (h : η.rtr i.rtr =i.rcn= rtr') :
    (η.run_locally i).update_reactor i.rtr {reactor . input := rtr'.input, .. (η.run_locally i).rtr i.rtr} = 
    (η.update_reactor i.rtr rtr').run_locally i :=
    begin
      have hq₁, from run_locally_equiv η i,
      have hq₂, from update_reactor_equiv (reactor.eq_rel_to_equiv h),
      have hq, from graph.equiv_trans hq₁ (graph.equiv_symm hq₂),
      simp only [(≈)] at hq,
      obtain ⟨hₑ, hᵢ, hᵣ⟩ := hq,
      ext1,
        {
          cases ((η.update_reactor i.rtr rtr').run_locally i).ids,
          exact hᵢ,
        },
        {
          unfold run_locally,
          have h', from reactor.eq_rel_to_symm (update_reactor_eq_rel_to h),
          have hc, from reactor.run_update_inputs_comm h',
          rw ←hc,
          repeat { rw [update_reactor_eq_rtr, update_reactor_same] }
        },
        {
          cases ((η.update_reactor i.rtr rtr').run_locally i).edges,
          exact hₑ,
        }
    end

















  lemma update_reactor_out_inv (η : graph υ) (i : reactor.id) (rtr : reactor υ) (h : rtr.output = (η.rtr i).output) :
    ∀ o, (η.update_reactor i rtr).port role.output o = η.port role.output o :=
    begin
      intro o,
      unfold output,
      suffices h : ((η.update_reactor i rtr).data o.rtr).output = (η.data o.rtr).output, { rw h },
      unfold update_reactor digraph.update_data,
      simp,
      rw function.update_apply,
      by_cases hᵢ : o.rtr = i,
        {
          rw [if_pos hᵢ, hᵢ],
          exact h
        },
        rw if_neg hᵢ
    end

  lemma update_input_out_inv (η : graph υ) (p : port.id) (v : option υ) :
    ∀ o, (η.update_port role.input p v).port role.output o = η.port role.output o :=
    begin
      unfold update_input,
      apply update_reactor_out_inv,
      refl,
    end

  lemma update_reactor_comm {i i' : reactor.id} (h : i ≠ i') (r r' : reactor υ) (η : graph υ) :
    (η.update_reactor i r).update_reactor i' r' = (η.update_reactor i' r').update_reactor i r :=
    begin
      unfold update_reactor,
      apply digraph.update_data_comm,
      exact h,
    end 

  lemma update_input_comm {i i' : port.id} (h : i ≠ i') (v v' : option υ) (η : graph υ) :
    (η.update_input i v).update_input i' v' = (η.update_input i' v').update_input i v :=
    sorry

  lemma update_reactor_eq (η : network.graph υ) (i : reactor.id) (rtr : reactor υ) :
    (η.update_reactor i rtr).rtr i = rtr :=
    by simp [graph.rtr, update_reactor, digraph.update_data]

  lemma update_reactor_neq (η : network.graph υ) {i i' : reactor.id} (rtr : reactor υ) (h : i' ≠ i):
    (η.update_reactor i rtr).rtr i' = η.rtr i' :=
    begin
      simp only [graph.rtr, update_reactor, digraph.update_data],
      apply function.update_noteq,
      exact h
    end

  lemma update_input_eq_rel (η : network.graph υ) (p : port.id) (v : option υ) (i : reaction.id) :
    ¬(rcn_dep_on_prt η i p) → (η.rtr i.rtr).eq_rel_to ((η.update_input p v).rtr i.rtr) i.rcn :=
    begin
      intro h,
      unfold update_input,
      unfold rcn_dep_on_prt at h,
      by_cases h_c : p.rtr = i.rtr,
        {
          rw [h_c, update_reactor_eq],
          simp at h,
          exact reactor.update_input_eq_rel _ (h h_c)
        },
        {
          rw (update_reactor_neq _ _ (ne.symm h_c)),
          apply eq_rel_to_refl
        }
    end

end graph
end network