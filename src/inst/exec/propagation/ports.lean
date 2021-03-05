import inst.network.graph
import inst.exec.propagation.port

open reactor.ports
open network

variables {υ : Type*} [decidable_eq υ]

-- For all edges `e` with `e.src ∈ p`, set `e.dst` to `rtr.output.nth e.src`.  
noncomputable def propagate_ports : network.graph υ → list port.id → network.graph υ :=
  list.foldl propagate_port

lemma propagate_ports_out_inv (η : network.graph υ) {p : list port.id}  :
  ∀ o, (propagate_ports η p).port role.output o = η.port role.output o :=
  begin
    intro o,
    unfold propagate_ports,
    induction p generalizing η,
      simp,
      rw [list.foldl_cons, p_ih, propagate_port_out_inv]
  end

lemma propagate_ports_comm (η : network.graph υ) (p p' : list port.id) (hᵤ : η.has_unique_port_ins) (hₚ : p' ~ p) :
  propagate_ports η p = propagate_ports η p' :=
  begin
    unfold propagate_ports,
    induction hₚ generalizing η,
      case list.perm.nil {
        refl,
      },
      case list.perm.cons : _ _ _ _ hᵢ {
        unfold list.foldl,
        apply hᵢ (propagate_port η hₚ_x), 
        exact propagate_port_unique_ins_inv _ _ hᵤ
      },
      case list.perm.swap {
        unfold list.foldl,
        rw propagate_port_comm η _ _ hᵤ
      },
      case list.perm.trans : l₁ l₂ l₃ p₁ p₂ hᵢ₁ hᵢ₂ {
        exact (hᵢ₂ _ hᵤ).trans (hᵢ₁ _ hᵤ)
      }
  end

lemma propagate_ports_comm' (η : network.graph υ) (p p' : list port.id) (hᵤ : η.has_unique_port_ins) :
  propagate_ports (propagate_ports η p) p' = propagate_ports (propagate_ports η p') p :=
  begin
    unfold propagate_ports,
    conv_lhs { rw ←list.foldl_append },
    conv_rhs { rw ←list.foldl_append },
    apply propagate_ports_comm _ _ _ hᵤ list.perm_append_comm
  end 

lemma propagate_ports_equiv (η η' : network.graph υ) (p : list port.id) (h : η ≈ η') :
  propagate_ports η p ≈ η' :=
  begin
    induction p with pₕ pₜ hᵢ generalizing η,
      case list.nil {
        unfold propagate_ports,
        exact h
      },
      case list.cons {
        unfold propagate_ports,
        have hₑ, from propagate_port_equiv η pₕ,
        have hₑ', from graph.equiv_trans hₑ h,
        have hᵢ', from hᵢ (propagate_port η pₕ),
        exact hᵢ' hₑ'
      }
  end