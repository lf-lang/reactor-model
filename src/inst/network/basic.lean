import inst.network.graph
import inst.prec.basic
import inst.prec.lemmas

open network

@[ext]
structure network (υ : Type*) [decidable_eq υ] :=
  (η : network.graph υ)
  (unique_ins : η.has_unique_port_ins)
  (prec_acyclic : η.is_prec_acyclic) -- In the long term this should be temporary.
  
variables {υ : Type*} [decidable_eq υ]

namespace network

  @[reducible]
  instance mem : has_mem graph.edge (network υ) := {mem := λ e n, e ∈ n.η.edges}

  instance equiv : has_equiv (network υ) := ⟨λ n n', n.η ≈ n'.η⟩

  instance : is_equiv (network υ) (≈) := 
    {
      symm := begin simp [(≈)], finish end,
      trans := begin simp [(≈)], finish end,
      refl := by simp [(≈)]
    }

  lemma edge_mem_equiv_trans {n n' : network υ} {e : graph.edge} :
    n' ≈ n → e ∈ n → e ∈ n' :=
    begin
      intros hₑ hₘ,
      simp [(≈)] at hₑ,
      simp [(∈)],
      rw hₑ.left,
      apply hₘ
    end

  noncomputable def update_input (n : network υ) (p : port.id) (v : option υ) : network υ :=
    {
      η := n.η.update_input p v,
      unique_ins := graph.edges_inv_unique_port_ins_inv (refl _) n.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (symm (graph.update_input_equiv _ _ _)) n.prec_acyclic
    }

  noncomputable def update_output (n : network υ) (p : port.id) (v : option υ) : network υ :=
    {
      η := n.η.update_output p v,
      unique_ins := graph.edges_inv_unique_port_ins_inv (refl _) n.unique_ins,
      prec_acyclic := graph.equiv_prec_acyc_inv (symm (graph.update_output_equiv _ _ _)) n.prec_acyclic
    }

  noncomputable def clear_ports_excluding (n : network υ) (i : finset port.id) (o : finset port.id) : network υ :=
    {
      η := n.η.clear_ports_excluding i o,
      unique_ins := sorry, -- TIME
      prec_acyclic := sorry -- TIME
    }

end network