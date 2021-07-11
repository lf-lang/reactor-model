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
    noncomputable def impl.rcns_for (σ : inst.network υ) (i : reactor.id) : finset reaction.id :=
      (σ.rtr i).priorities.image (reaction.id.mk i)

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.internal_reaction_pairs (σ : inst.network υ) (rtr : reactor.id) : finset (reaction.id × reaction.id) :=
      (finset.product (impl.rcns_for σ rtr) (impl.rcns_for σ rtr)).filter (λ p, p.1.rcn > p.2.rcn)

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.internal_edges (σ : inst.network υ) : finset prec.graph.edge :=
      σ.ids.bUnion (λ rtr, (impl.internal_reaction_pairs σ rtr).image (λ p, ⟨p.1, p.2⟩))

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.external_reaction_pairs (σ : inst.network υ) : finset (reaction.id × reaction.id) :=
      σ.ids.bUnion (λ rtr, finset.product (impl.rcns_for σ rtr) (impl.rcns_for σ rtr))

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.external_edges (σ : inst.network υ) : finset prec.graph.edge :=
      (impl.external_reaction_pairs σ).bUnion (λ p, 
        (finset.product (σ.deps p.1 role.output) (σ.deps p.2 role.input)).bUnion (λ q,
          if (network.graph.edge.mk q.1 q.2) ∈ σ.edges then {prec.graph.edge.mk p.1 p.2} else ∅
        )
      )

    -- *Some* concrete implementation of a `prec_func` algorithm.
    noncomputable def implementation : inst.network υ → prec.graph υ := λ σ,
      { lgraph . 
        ids := σ.ids.bUnion (λ rtr, impl.rcns_for σ rtr),        
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
              simp only [impl.internal_reaction_pairs, finset.mem_filter, finset.mem_product] at hp,
              rw ←he,
              split,
                exact ⟨r, hr, hp.1.1⟩,
                exact ⟨r, hr, hp.1.2⟩
            },
            { 
              simp only [impl.external_edges, finset.mem_bUnion, finset.mem_image] at he,
              obtain ⟨r, hr, p, hp, he⟩ := he,
              simp only [impl.external_reaction_pairs, finset.mem_bUnion, finset.mem_product] at hr,
              obtain ⟨x, hm, hx⟩ := hr,
              split,
                {
                  existsi x,
                  existsi hm,
                  simp only [lgraph.edge.lsrc],
                  split_ifs at he,
                    {
                      simp at he,
                      simp only [he],
                      exact hx.1
                    },
                    {
                      by_contradiction,
                      have h, from finset.not_mem_empty e,
                      contradiction
                    }
                },
                {
                  existsi x,
                  existsi hm,
                  simp only [lgraph.edge.ldst],
                  split_ifs at he,
                    {
                      simp at he,
                      simp only [he],
                      exact hx.2
                    },
                    {
                      by_contradiction,
                      have h, from finset.not_mem_empty e,
                      contradiction
                    }
                },
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
