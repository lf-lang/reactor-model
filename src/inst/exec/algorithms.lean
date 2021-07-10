import topo
import inst.network.basic 
import inst.primitives
open reactor.ports

open_locale classical

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

namespace inst
namespace network

  -- A function that can generate a well-formed precedence graph for a given instantaneous network.
  @[ext]
  structure prec_func :=
    (func : inst.network υ → prec.graph υ)
    (well_formed : ∀ σ, func σ ⋈ σ.η)

  -- A function that can generate a complete topological ordering for a given precedence graph.
  structure topo_func :=
    (func : prec.graph υ → list reaction.id)
    (is_topo : ∀ {σ : inst.network υ} {ρ : prec.graph υ} (h : ρ ⋈ σ.η), (func ρ).is_complete_topo_over ρ)

  variable {υ}

  namespace prec_func

    -- Calling an instance of `prec_func` as a function, means calling its `func`.
    instance coe_to_fun : has_coe_to_fun (prec_func υ) := ⟨_, (λ f, f.func)⟩

    -- The precedence function is unique.
    theorem unique (p p' : prec_func υ) : p = p' :=
      begin
        rw prec_func.ext p p',
        funext σ,
        exact prec.wf_prec_graphs_are_eq (p.well_formed σ) (p'.well_formed σ)
      end

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.reaction_pairs (σ : inst.network υ) (rtr : reactor.id) : finset (reaction.id × reaction.id) :=
      (finset.product (σ.η.rcns_for rtr) (σ.η.rcns_for rtr)).filter (λ p, p.1.rcn > p.2.rcn)

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.internal_edges (σ : inst.network υ) : finset prec.graph.edge :=
      σ.ids.bUnion (λ rtr, (impl.reaction_pairs σ rtr).image (λ p, ⟨p.1, p.2⟩))

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.external_edges (σ : inst.network υ) : finset prec.graph.edge :=
      σ.edges.bUnion (λ e, (finset.product (σ.rcns_dep_to role.output e.src) (σ.rcns_dep_to role.input e.dst)).image (λ p, ⟨p.1, p.2⟩))

    -- *Some* concrete implementation of a `prec_func` algorithm.
    noncomputable def implementation : inst.network υ → prec.graph υ := λ σ,
      { lgraph . 
        ids := σ.ids.bUnion (λ rtr, σ.η.rcns_for rtr),
        data := σ.η.rcn,
        edges := impl.internal_edges σ ∪ impl.external_edges σ,
        well_formed := begin
          unfold finset.are_well_formed_over,
          intros e he,
          repeat { rw finset.mem_bUnion },
          rw finset.mem_union at he,
          cases he,
            {
              simp only [impl.internal_edges, finset.mem_bUnion, finset.mem_image] at he,
              obtain ⟨r, hr, p, hp, he⟩ := he,
              simp only [impl.reaction_pairs, finset.mem_filter, finset.mem_product] at hp,
              rw ←he,
              split,
                exact ⟨r, hr, hp.1.1⟩,
                exact ⟨r, hr, hp.1.2⟩
            },
            { 
              unfold impl.external_edges at he,
              simp only [impl.external_edges, finset.mem_bUnion, finset.mem_image] at he,
              obtain ⟨c, hc, p, hp, he⟩ := he,
              simp only [finset.mem_product] at hp,
              rw ←he,
              clear he,
              have hw, from σ.η.well_formed,
              simp only [finset.are_well_formed_over] at hw,
              unfold edges at hc,
              replace hw := hw c hc,
              clear hc,
              split,
                {
                  /-existsi lgraph.edge.lsrc c,
                  existsi hw.1,
                  simp only [lgraph.edge.lsrc],
                  -- unfold graph.rcns_for,
                  -- simp only [finset.mem_image],
                  have HH, from (rcn_dep_to_prt_iff_prt_dep_of_rcn.mp hp.1),
                  have HHH, from graph.mem_deps_iff_mem_rcn_deps.mp HH,
                  unfold rcns_dep_to at hp,
                  rw ←HHH.1,
                  simp only [finset.mem_image] at hp,
                  obtain ⟨⟨a, ha, hae⟩, _⟩ := hp,
                  generalize_proofs ha' at ha,
                  simp at ha,
                  unfold reactor.rcns_dep_to at ha,
                  simp at ha,
                  have H : p.fst.rcn = a, from sorry,
                  rw ←H at ha,-/
                  sorry,                  
                },
                sorry
                -- exact ⟨lgraph.edge.lsrc c, hw.1, graph.deps_mem_rtr_rcns_mem (rcn_dep_to_prt_iff_prt_dep_of_rcn.mp hp.1)⟩,
                -- exact ⟨lgraph.edge.ldst c, hw.2, graph.deps_mem_rtr_rcns_mem (rcn_dep_to_prt_iff_prt_dep_of_rcn.mp hp.2)⟩
            }
        end  
      }

    -- There exists an instance of (an algorithm for) `prec_func`.
    -- This is used to define a parameter-free version of `run` (called `run'`).
    noncomputable instance inhabited : inhabited (prec_func υ) := ⟨{ prec_func .
      func := prec_func.implementation,
      well_formed := sorry,
    }⟩

  end prec_func
  
  namespace topo_func

    -- Calling an instance of `topo_func` as a function, means calling its `func`.
    instance coe_to_fun : has_coe_to_fun (topo_func υ) := ⟨_, (λ f, f.func)⟩

    -- There exists an instance of (an algorithm for) `topo_func`.
    -- This is used to define a parameter-free version of `run` (called `run'`).
    instance inhabited : inhabited (topo_func υ) := sorry

  end topo_func

end network
end inst
