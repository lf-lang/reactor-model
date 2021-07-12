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
    noncomputable def impl.internal_reaction_pairs (σ : inst.network υ) (rtr : reactor.id) : finset (reaction.id × reaction.id) :=
      (finset.product (σ.rcns_for rtr) (σ.rcns_for rtr)).filter (λ p, p.1.rcn > p.2.rcn)

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.internal_edges (σ : inst.network υ) : finset prec.graph.edge :=
      σ.ids.bUnion (λ rtr, (impl.internal_reaction_pairs σ rtr).image (λ p, ⟨p.1, p.2⟩))

    -- An implementation detail of `prec_func.implementation`.
    noncomputable def impl.external_edges (σ : inst.network υ) : finset prec.graph.edge :=
      (finset.product σ.η.rcn_ids σ.η.rcn_ids).bUnion (λ p, 
        (finset.product (σ.deps p.1 role.output) (σ.deps p.2 role.input)).bUnion (λ q,
          if (network.graph.edge.mk q.1 q.2) ∈ σ.edges then {prec.graph.edge.mk p.1 p.2} else ∅
        )
      )

    -- *Some* concrete implementation of a `prec_func` algorithm.
    noncomputable def implementation : inst.network υ → prec.graph υ := λ σ,
      { lgraph . 
        ids := σ.ids.bUnion (λ rtr, σ.rcns_for rtr),        
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
              simp only [graph.rcn_ids, finset.mem_bUnion, finset.mem_product] at hr,
              split,
                work_on_goal 0 { obtain ⟨x, hm, hx⟩ := hr.1 },
                work_on_goal 1 { obtain ⟨x, hm, hx⟩ := hr.2 },
                all_goals {                 
                  existsi x,
                  existsi hm
                },
                work_on_goal 0 { simp only [lgraph.edge.lsrc] },
                work_on_goal 1 { simp only [lgraph.edge.ldst] },
                all_goals { 
                  split_ifs at he,
                  work_on_goal 1 { 
                    by_contradiction,
                    have h, from finset.not_mem_empty e,
                    contradiction
                  },
                  simp at he,
                  simp only [he],
                  exact hx
                }
            }
        end  
      }

    -- There exists an instance of (an algorithm for) `prec_func`.
    -- This is used to define a parameter-free version of `run` (called `run'`).
    noncomputable instance inhabited : inhabited (prec_func υ) := ⟨{ prec_func .
      func := prec_func.implementation,
      well_formed := begin
        intro σ,
        unfold implementation prec.graph.is_well_formed_over,
        repeat { split },
          {
            unfold prec.graph.ids_are_well_formed_over,
            intro i,
            simp,
            unfold ids,
            split,
              {
                intro h,
                obtain ⟨r, hr⟩ := h,
                have h, from rcns_for_def.mp hr.2,
                rw h.1,
                exact ⟨hr.1, h.2⟩
              },
              {
                intro h,
                existsi i.rtr,
                existsi h.1,
                rw rcns_for_def,
                unfold rtr,
                exact ⟨refl _, h.2⟩
              }
          },
          {
            unfold prec.graph.data_is_well_formed_over prec.graph.rcn,
            intro i,
            refl
          },
          {
            unfold prec.graph.edges_are_well_formed_over,
            intro e,
            simp,
            split,
              {
                intros h,
                cases h,
                  {
                    simp only [impl.internal_edges, finset.mem_bUnion] at h,
                    obtain ⟨r, hr, hm⟩ := h,
                    simp only [finset.mem_image] at hm,
                    obtain ⟨p, hp, he⟩ := hm,
                    simp only [impl.internal_reaction_pairs, finset.mem_filter, finset.mem_product] at hp,
                    unfold prec.graph.internally_dependent,
                    have ht1, from rcns_for_def.mp hp.1.1,
                    have ht2, from rcns_for_def.mp hp.1.2,
                    simp only [←he, ht1.1, ht2.1],
                    exact ⟨⟨r, hr, hp.1.1⟩, ⟨r, hr, hp.1.2⟩, or.inl ⟨refl _, hp.2⟩⟩
                  },
                  {
                    simp only [impl.external_edges, finset.mem_bUnion] at h,
                    obtain ⟨r, hr, p, hp, h⟩ := h,
                    simp only [finset.mem_bUnion, finset.mem_product] at hr,
                    simp only [finset.mem_product] at hp,
                    unfold prec.graph.externally_dependent,
                    split_ifs at h with hi,
                    work_on_goal 1 {
                      by_contradiction,
                      have hc, from finset.not_mem_empty e,
                      contradiction
                    },
                    simp at h,
                    simp only [h],
                    repeat { rw graph.rcn_ids_def at hr },
                    split, exact ⟨r.1.rtr, hr.1.1, graph.rcns_for_def.mpr ⟨refl _, hr.1.2⟩⟩,
                    split, exact ⟨r.2.rtr, hr.2.1, graph.rcns_for_def.mpr ⟨refl _, hr.2.2⟩⟩, 
                    right,
                    existsi { graph.edge . src := p.fst, dst := p.snd },
                    split, exact hi,
                    exact hp
                  }
              },
              {
                intros h,
                obtain ⟨⟨r1, hm1, ha1⟩, ⟨r2, hm2, ha2⟩, h⟩ := h,
                simp only [rcns_for, graph.rcns_for_def] at ha1 ha2,
                cases h,
                  {
                    unfold prec.graph.internally_dependent at h,
                    simp only [impl.internal_edges, finset.mem_bUnion],
                    left,
                    existsi e.src.rtr,
                    rw ←ha1.1 at hm1,
                    existsi hm1,
                    simp only [finset.mem_image],
                    existsi (e.src, e.dst),
                    suffices hg : (e.src, e.dst) ∈ impl.internal_reaction_pairs σ e.src.rtr, {
                      existsi hg,
                      ext ; refl
                    },
                    simp only [impl.internal_reaction_pairs, finset.mem_filter, finset.mem_product],
                    obtain ⟨ha1l, ha1r⟩ := ha1,
                    obtain ⟨ha2l, ha2r⟩ := ha2,
                    rw ←ha1l at ha1r,
                    have hg, from graph.rcns_for_def.mpr ⟨refl _, ha1r⟩,
                    rw ←(eq.trans h.1 ha2l) at ha2r,
                    have hg', from graph.rcns_for_def.mpr ⟨(symm h.1), ha2r⟩,
                    exact ⟨⟨hg, hg'⟩, h.2⟩
                  },
                  {
                    right,
                    unfold prec.graph.externally_dependent at h,
                    obtain ⟨x, hm, hx⟩ := h,
                    simp only [impl.external_edges, finset.mem_bUnion],
                    existsi (e.src, e.dst),
                    obtain ⟨ha1l, ha1r⟩ := ha1,
                    obtain ⟨ha2l, ha2r⟩ := ha2,
                    rw ←ha1l at hm1 ha1r,
                    rw ←ha2l at hm2 ha2r,
                    have hi1, from graph.rcn_ids_def.mpr ⟨hm1, ha1r⟩,
                    have hi2, from graph.rcn_ids_def.mpr ⟨hm2, ha2r⟩,
                    existsi (@finset.mem_product _ _ _ _ (e.src, e.dst)).mpr ⟨hi1, hi2⟩,
                    existsi (x.src, x.dst),
                    existsi (@finset.mem_product _ _ _ _ (x.src, x.dst)).mpr hx,
                    split_ifs with hi,
                      { simp, ext1 ; refl },
                      {
                        have he : x = {src := x.src, dst := x.dst}, { ext1 ; refl },
                        have hc : x ∉ σ.η.edges, { rw he, exact hi },
                        contradiction
                      }
                  }
              }
          }
      end
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
