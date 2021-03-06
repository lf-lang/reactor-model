import inst.prec
open reactor
open network

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

  -- Forwards the `edges` property from the network graph to the network.
  noncomputable def edges (σ : network υ) := σ.η.edges

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

end network
end inst