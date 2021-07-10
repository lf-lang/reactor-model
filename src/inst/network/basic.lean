import inst.network.prec
open reactor

-- Cf. inst/primitives.lean
variables (υ : Type*) [decidable_eq υ]

-- An instantaneous reactor network is an instantaneous reactor network graph with the constraints
-- of having unique input-port connections as well as being precedence-acyclic.
@[ext]
structure inst.network :=
  (η : inst.network.graph υ)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic)
  
variables {υ}

namespace inst
namespace network

  -- A lifted version of `inst.network.graph.ids`.
  noncomputable def ids (σ : network υ) := σ.η.ids

  -- A lifted version of `inst.network.graph.edges`.
  noncomputable def edges (σ : network υ) := σ.η.edges

  -- A lifted version of `inst.network.graph.rtr`.
    noncomputable def rtr (σ : network υ) : reactor.id → reactor υ := σ.η.rtr

  -- A lifted version of `inst.network.graph.port`.
  noncomputable def port (σ : network υ) : ports.role → port.id → option υ := σ.η.port

  -- A lifted version of `inst.network.graph.port'`.
  noncomputable def port' (σ : network υ) : ports.role → port.id → option (option υ) := σ.η.port'

  -- A lifted version of `inst.network.graph.deps`.
  noncomputable def deps (σ : network υ) : reaction.id → ports.role → finset port.id := σ.η.deps

  -- A lifted version of `reactor.rcns_dep_to`.
  noncomputable def rcns_dep_to (σ : inst.network υ) (r : ports.role) (p : port.id) : finset reaction.id :=
    (reactor.rcns_dep_to_finite (σ.rtr p.rtr) r p.prt).to_finset.image (reaction.id.mk p.rtr)

  -- A lifted version of `reactor.rcn_dep_to_prt_iff_prt_dep_of_rcn`.
  lemma rcn_dep_to_prt_iff_prt_dep_of_rcn {σ : inst.network υ} {r : ports.role} {p : port.id} {rcn : reaction.id} : 
    (rcn ∈ σ.rcns_dep_to r p) ↔ (p ∈ σ.deps rcn r) :=
    begin
      unfold rcns_dep_to,
      rw finset.mem_image,
      split,
        {
          intro h,
          obtain ⟨x, hm, he⟩ := h,
          unfold deps graph.deps graph.rcn,
          rw finset.mem_image,
          rw set.finite.mem_to_finset at hm,
          replace hm := reactor.rcn_dep_to_prt_iff_prt_dep_of_rcn.mp hm,
          have hx : rcn.rcn = x, by finish,
          rw ←hx at hm,
          have hr : rcn.rtr = p.rtr, by finish,
          rw hr,
          have hp : port.id.mk p.rtr p.prt = p, { ext ; refl },
          exact ⟨p.prt, hm, hp⟩
        },
        {
          intro h,
          existsi rcn.rcn,
          unfold deps graph.deps at h,
          rw set.finite.mem_to_finset,
          rw finset.mem_image at h,
          obtain ⟨x, hx, he⟩ := h,
          split,
            {
              apply reactor.rcn_dep_to_prt_iff_prt_dep_of_rcn.mpr,
              unfold inst.network.graph.rcn at hx,
              have hp : p.prt = x, by finish,
              have hr : p.rtr = rcn.rtr, by finish,
              simp only [inst.network.rtr, hp, hr, hx]
            },
            {
              rw ←he,
              ext ; refl
            }
        }
    end

  -- The set of occupied port-IDs in the network.
  def port_ids (σ : network υ) (r : ports.role) : set port.id :=
    -- `p.prt < ...` means that `p.prt` is valid index in the port list.
    { p : port.id | (p.rtr ∈ σ.η.ids) ∧ (p.prt < ((σ.η.rtr p.rtr).prts r).length) }

  -- Forwards equivalence from the network graph to the network.
  instance equiv : has_equiv (network υ) := ⟨λ σ σ', σ.η ≈ σ'.η⟩

  -- Network equivalence is reflexive.
  @[refl] 
  lemma equiv_refl (σ : network υ) : σ ≈ σ := by refl

  -- Network equivalence is symmetric.
  @[symm]
  lemma equiv_symm {σ σ' : network υ} (h : σ ≈ σ') : σ' ≈ σ :=
    by { simp only [(≈)] at h ⊢, simp [h] }

  -- Network equivalence is transitive.
  @[trans]
  lemma equiv_trans {σ₁ σ₂ σ₃ : network υ} (h₁₂ : σ₁ ≈ σ₂) (h₂₃ : σ₂ ≈ σ₃) : σ₁ ≈ σ₃ :=
    by { simp [(≈)] at ⊢ h₁₂ h₂₃, simp [h₁₂, h₂₃] }

  -- Forwards the `update_port` function from the network graph to the network.
  noncomputable def update_port (σ : network υ) (r : ports.role) (p : port.id) (v : option υ) : network υ :=
    {
      η := σ.η.update_port r p v,
      unique_ins := graph.eq_edges_unique_port_ins (refl _) σ.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.update_port_equiv _ _ _ _) σ.prec_acyclic
    }

  -- Forwards the equivalence of `update_port` from the network graph to the network.
  lemma update_port_equiv (σ : network υ) (r : ports.role) (p : port.id) (v : option υ) : σ.update_port r p v ≈ σ :=
    by { unfold update_port, exact equiv_symm (graph.update_port_equiv _ _ _ _) }

  -- Forwards the `clear_all_ports` function from the network graph to the network.
  noncomputable def clear_all_ports (σ : inst.network υ) : inst.network υ :=
    {
      η := σ.η.clear_all_ports,
      unique_ins := graph.eq_edges_unique_port_ins (symm (graph.clear_all_ports_equiv _).left) σ.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.equiv_symm (graph.clear_all_ports_equiv _)) σ.prec_acyclic
    }

  -- Forwards the equivalence of `clear_all_ports` from the network graph to the network.
  lemma clear_all_ports_equiv (σ : inst.network υ) : σ.clear_all_ports ≈ σ :=
    by { unfold clear_all_ports, exact graph.clear_all_ports_equiv _ }

  -- Forwards the `copy_ports` function from the network graph to the network.
  noncomputable def copy_ports (σ σ' : inst.network υ) (ps : finset port.id) (r : ports.role) : inst.network υ :=
    {
      η := σ.η.copy_ports σ'.η ps r,
      unique_ins := graph.eq_edges_unique_port_ins (symm (graph.copy_ports_equiv _ _ _ _).left) σ.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (graph.equiv_symm (graph.copy_ports_equiv _ _ _ _)) σ.prec_acyclic
    }

  -- Forwards the equivalence of `copy_ports` from the network graph to the network.
  lemma copy_ports_equiv (σ σ' : inst.network υ) (ps : finset port.id) (r : ports.role) : σ.copy_ports σ' ps r ≈ σ :=
    by { unfold copy_ports, exact graph.copy_ports_equiv _ _ _ _ }

end network
end inst