import lgraph
import inst.network.graph
open reactor.ports

open_locale classical

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

namespace inst.network

  -- An edge in a precedence graph connects reactions.
  @[ext]
  structure prec_graph.edge := 
    (src : reaction.id)
    (dst : reaction.id)

  -- Precedence graph edges are directed.
  instance prec_graph.lgraph_edge : lgraph.edge prec_graph.edge reaction.id := 
    { lsrc := prec_graph.edge.src, ldst := prec_graph.edge.dst }

  variable {υ}

  def rcns_are_internally_dep (i i' : reaction.id) : Prop := 
    (i.rtr = i'.rtr) ∧ (i.rcn > i'.rcn)

  def rcns_are_externally_dep_in (i i' : reaction.id) (γ : graph υ) : Prop :=
    ∃ e : inst.network.edge, (e ∈ γ.edges) ∧ (e.src ∈ γ.deps i role.out) ∧ (e.dst ∈ γ.deps i' role.in)

  structure prec_graph (γ : graph υ) extends (lgraph reaction.id (reaction υ) prec_graph.edge) :=
    (wf_ids : to_lgraph.ids = γ.rcn_ids)
    (wf_data : ∀ i, to_lgraph.nodes.lookup i = γ.rcn i)
    (wf_edges : 
      ∀ e : prec_graph.edge, e ∈ to_lgraph.edges ↔ 
        (e.src ∈ to_lgraph.ids) ∧ -- IS THIS NECESSARY? AFTER ALL, LGRAPH ALREADY ENFORCES THIS.
        (e.dst ∈ to_lgraph.ids) ∧ 
        (rcns_are_internally_dep e.src e.dst ∨ rcns_are_externally_dep_in e.src e.dst γ)
    )

  namespace prec_graph

    noncomputable def ids {γ : graph υ} (ρ : prec_graph γ) := ρ.to_lgraph.ids
    def has_path_from_to {γ : graph υ} (ρ : prec_graph γ) (i i' : reaction.id) : Prop := i'~ρ.to_lgraph~>i
    notation i~ρ~>j := ρ.has_path_from_to i j

    -- Two reactions are independent in a precedence graph if there are no paths between them.
    -- This property trivially holds for all reactions that are not part of the precedence graph.
    -- Hence most uses of this property should also constrain `i` and `i'` to be `∈ ρ.ids`.
    def indep {γ : graph υ} (ρ : prec_graph γ) (i i' : reaction.id) : Prop := ¬(i~ρ~>i') ∧ ¬(i'~ρ~>i)

  end prec_graph

  -- The proposition, that every well-formed precedence graph over a network is acyclic.
  def graph.is_prec_acyclic (γ : inst.network.graph υ) : Prop :=
    ∀ ρ : prec_graph γ, ρ.to_lgraph.is_acyclic

end inst.network
