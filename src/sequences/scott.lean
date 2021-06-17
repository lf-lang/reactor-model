import data.seq.seq
import order.omega_complete_partial_order
import data.list

#check seq
#check omega_complete_partial_order
#check partial_order

namespace seq_kahn
variable α : Type*
variables s₁ s₂ : seq α

-- preorder:

def seq_finite (s : seq α) := ∃ N : ℕ, s.1 N = none
def seq_prefix {α : Type*} (s t : (seq α)) := ∀ n a, s.val n = some a → t.val n = some a
instance seq.has_le {α : Type*} : has_le (seq α) := ⟨seq_prefix⟩

theorem seq_prefix_refl {α : Type*} : ∀ (s : seq α), s ≤ s := by tauto
  
theorem seq_prefix_trans {α : Type*} : ∀ (a b c : seq α), a ≤ b → b ≤ c → a ≤ c := by tauto

instance seq.preorder {α : Type*} : preorder (seq α) :=
{le := seq_prefix,
le_refl := seq_prefix_refl,
le_trans := seq_prefix_trans
}


-- ω cpo: 
-- the construction is i ↦ a s.t. (∀ N, (∀ n ≥ N, (ch n).val i = a)
lemma seq_chain_stable_some {α : Type*} (ch : omega_complete_partial_order.chain (seq α))
(i N : ℕ) (a : α) : (ch N).val i = some a → ∀ n ≥ N, (ch n).val i = some a :=
begin
intro h,
intros n ngeqN,
by_contradiction hc, --is this necessary?
have seqs_le : (ch N) ≤ (ch n), by
{
  begin
    have Nleqn : N ≤ n, by exact ge_iff_le.mp ngeqN,
    have ch_mon : monotone ch, by refine preorder_hom.monotone _,
    exact ch_mon Nleqn, 
  end 
},
exact hc (seqs_le i a h),
end

lemma seq_chain_well_def {α : Type*} (ch : omega_complete_partial_order.chain (seq α)) :
∀ (i : ℕ), (∃ N a, (∀ n ≥ N, (ch n).val i = a)) :=
begin
intro i,
sorry,
end

def seq.ωSup {α : Type*} (ch : omega_complete_partial_order.chain (seq α)) :=   -- set to: seq.val m = a
--⟨ (λ i, (a : option α, (∀ N a, (∀ n ≥ N, (ch n).val i = a))) ,  ⟩
ch 1 --sorry
--ωSup : omega_complete_partial_order.chain α → α
--le_ωSup : ∀ (c_1 : omega_complete_partial_order.chain α) (i : ℕ), ⇑c_1 i ≤ omega_complete_partial_order.ωSup c_1
--ωSup_le : ∀ (c_1 : omega_complete_partial_order.chain α) (x : α), (∀ (i : ℕ), ⇑c_1 i ≤ x) → omega_complete_partial_order.ωSup c_1 ≤ x)

-- class omega_complete_partial_order (α : Type*) extends partial_order α :=
-- (ωSup     : chain α → α)
-- (le_ωSup  : ∀(c:chain α), ∀ i, c i ≤ ωSup c)
-- (ωSup_le  : ∀(c:chain α) x, (∀ i, c i ≤ x) → ωSup c ≤ x)


lemma seq_chain_le_ωSup {α : Type*} : ∀ (ch : omega_complete_partial_order.chain (seq α))
(i : ℕ), ch i ≤ seq.ωSup ch :=
begin
  sorry,
end

lemma seq_chain_ωSup_le {α : Type*} : ∀ (c_1 : omega_complete_partial_order.chain (seq α))
(x : seq α), (∀ (i : ℕ), c_1 i ≤ x) → seq.ωSup c_1 ≤ x :=
begin
  sorry,
end

instance seq.omega_complete_partial_order {α : Type*} : omega_complete_partial_order (seq α) := 
{ --to_partial_order := partial_order seq α,
 ωSup := seq.ωSup,
 le_ωSup := seq_chain_le_ωSup, 
 ωSup_le := seq_chain_ωSup_le}
