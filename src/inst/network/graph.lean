import lgraph
import inst.network.ids
open reactor
open reactor.ports
open reaction

open_locale classical

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

namespace inst.network

  @[ext]
  structure edge :=
    (src : port.id role.out)
    (dst : port.id role.in)

  -- Reactor network graph edges are directed.
  instance lgraph_edge : lgraph.edge inst.network.edge reactor.id := 
    { lsrc := port.id.rtr ∘ edge.src, ldst := port.id.rtr ∘ edge.dst }

  -- An instantaneous reactor network graph is an L-graph of reactors, identified by reactor-IDs
  -- and connected by the edges define above.
  structure graph extends l : lgraph reactor.id (reactor υ) edge :=
    (wf_edge_prts : 
      ∀ e : edge, e ∈ l.edges → 
        ∃ s, (l.nodes.lookup e.src.rtr = some s) ∧ (e.src.prt ∈ (s.prts role.out).ids) ∧
        ∃ d, (l.nodes.lookup e.dst.rtr = some d) ∧ (e.dst.prt ∈ (d.prts role.in).ids)
    )

  namespace graph

    variable {υ}

    def has_unique_port_ins (γ : graph υ) : Prop :=
      ∀ (e e' ∈ γ.edges), (e : edge).dst = e'.dst → e = e'

    theorem eq_edges_unique_port_ins {γ γ' : graph υ} (hₑ : γ.edges = γ'.edges) (hᵤ : γ.has_unique_port_ins) :
      γ'.has_unique_port_ins :=
      begin
        unfold has_unique_port_ins,
        intros e e',
        unfold has_unique_port_ins at hᵤ,
        simp [(∈)] at hᵤ ⊢,
        rw ←hₑ,
        apply hᵤ 
      end

    noncomputable def rcn_ids (γ : graph υ) : finset reaction.id := 
      let description := { i : reaction.id | ∃ rtr, (γ.nodes.lookup i.rtr = some rtr) ∧ (i.rcn ∈ rtr.rcn_ids) } in
      have is_finite : description.finite, from sorry,
      is_finite.to_finset

    noncomputable def rcn (γ : graph υ) (i : reaction.id) : option (reaction υ) :=
      (γ.nodes.lookup i.rtr) >>= (λ rtr, rtr.rcns.lookup i.rcn)

    noncomputable def deps (γ : graph υ) (i : reaction.id) (r : ports.role) : finset (port.id r) :=
      let description := { p : port.id r | p.rtr = i.rtr ∧ ∃ rcn, (γ.rcn i = some rcn) ∧ p.prt ∈ (rcn.deps r) } in
      have is_finite : description.finite, from sorry,
      is_finite.to_finset
      

  -- -- The dependencies of a given reaction for a given role, as proper `port.id`s.
  -- noncomputable def deps (η : graph υ) (i : reaction.id) (r : ports.role) : finset port.id :=
    -- ((η.rcn i).deps r).image (port.id.mk i.rtr)

  end graph

end inst.network

-- ONLY DEFINE THOSE PROPERTIES ON network.graph THAT ARE REQUIRED TO DEFINE THE CONSTRAINTS OF A NETWORK
-- THIS NOW SOLELY DEPENDS ON WHAT THE DEFINITION OF is_prec_acyclic REQUIRES.











  

  -- The reactor in a network graph, that is associated with a given reactor ID.
  noncomputable def rtr (η : network.graph υ) (i : reactor.id) : reactor υ := η.data i

  -- The port in a network graph, that is associated with a given role and port ID.
  noncomputable def port (η : graph υ) (r : ports.role) (i : port.id) : option υ :=
    (η.rtr i.rtr).port r i.prt

  -- A different version of `port` - cf. `reactor.port` vs. `reactor.port'`.
  noncomputable def port' (η : graph υ) (r : ports.role) (i : port.id) : option (option υ) :=
    (η.rtr i.rtr).port' r i.prt

  -- All of the reaction-IDs associated with a given reactor in a given network graph.
  noncomputable def rcns_for (η : graph υ) (i : reactor.id) : finset reaction.id :=
    (η.rtr i).priorities.image (reaction.id.mk i)

  lemma rcns_for_def {η : graph υ} {rcn : reaction.id} {rtr : reactor.id} :
    rcn ∈ η.rcns_for rtr ↔ (rcn.rtr = rtr ∧ rcn.rcn ∈ (η.rtr rtr).priorities) :=
    begin
      simp only [rcns_for, finset.mem_image],
      split,
        {
          intro h,
          obtain ⟨x, hx, he⟩ := h,
          split, finish,
          have h2 : rcn.rcn = x, by finish,  
          rw h2,
          exact hx,
        },
        {
          intro h,
          existsi rcn.rcn,
          existsi h.2,
          ext,
            exact symm h.1,
            refl
        }
    end

  lemma rcn_ids_def {η : graph υ} {rcn : reaction.id} :
    rcn ∈ η.rcn_ids ↔ (rcn.rtr ∈ η.ids ∧ rcn.rcn ∈ (η.rtr rcn.rtr).priorities) :=
    begin
      simp only [rcn_ids, finset.mem_bUnion],
      split,
        {
          intro h,
          obtain ⟨x, hx, hr⟩ := h,
          obtain ⟨y, hy⟩ := rcns_for_def.mp hr,
          rw ←y at hy hx,
          exact ⟨hx, hy⟩
        },
        {
          intro h,
          existsi rcn.rtr,
          existsi h.1,
          rw rcns_for_def,
          exact ⟨refl _, h.2⟩
        }
    end

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
          simp [port.id.mk, port.id.rtr, port.id.prt, ←hₚ, hₓ]
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
  lemma mem_eₒ {η : graph υ} (p : port.id) {e : edge} : e ∈ η.eₒ p ↔ e ∈ η.edges ∧ e.src = p :=
    by simp [eₒ, finset.mem_filter]

  -- Reactor network graphs' equality is non-constructively decidable.
  noncomputable instance dec_eq : decidable_eq graph.edge := classical.dec_eq _

  -- A reactor is a member of a network graph if the graph contains an ID that maps to it.
  instance rtr_mem : has_mem (reactor υ) (graph υ) := {mem := λ rtr η, ∃ i, η.data i = rtr}

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

  -- Equivalent network graphs have equal reaction-IDs.
  lemma equiv_eq_rcn_ids {η η' : graph υ} (h : η ≈ η') : η.rcn_ids = η'.rcn_ids :=
    begin
      simp [(≈)] at h,
      ext x,
      repeat { rw rcn_ids_def },
      rw [h.2.1, (h.2.2 x.rtr).1]
    end
