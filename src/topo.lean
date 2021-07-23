import lgraph
import mathlib
import logic.relator

variables {κ δ ε : Type*}
variables [decidable_eq κ] [decidable_eq δ] [lgraph.edge ε κ]

-- The definition of what it means for a given list to be a topological ordering for a given graph.
-- Note that this is not the same as a "complete" topological ordering (`list.is_complete_topo_over`).
-- 
-- `list`s with `nodup` are the formalization for finite ordered sets: 
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Ordered.20set
def list.is_topo_over (l : list κ) (g : lgraph κ δ ε) : Prop :=
  l.nodup ∧ ∀ k k' ∈ l, (k~g~>k') → (l.index_of k < l.index_of k')

namespace topo

  -- Removing an element from a topological ordering does not break the property of it being a topological ordering.
  lemma erase_is_topo {t : list κ} {g : lgraph κ δ ε} (k : κ) (h : t.is_topo_over g) :
    (t.erase k).is_topo_over g :=
    begin
      unfold list.is_topo_over at h ⊢,
      split,
        exact list.nodup_erase_of_nodup _ h.left,
        {
          intros x x' hₓ hₓ' hₚ,
          have hᵢ, from h.right x x' (list.mem_of_mem_erase hₓ) (list.mem_of_mem_erase hₓ') hₚ,
          exact list.index_of_erase_lt hᵢ hₓ hₓ' h.left
        }
    end

  -- If a list is a topological ordering for some graph, then so is its tail.
  lemma cons_is_topo {hd : κ} {tl : list κ} {g : lgraph κ δ ε} (h : (hd :: tl).is_topo_over g) :
    tl.is_topo_over g :=
    begin
      rw ←list.erase_cons_head hd tl,
      exact erase_is_topo hd h
    end

end topo

-- A topological ordering is "complete" if it contains all of its graph's vertices.
def list.is_complete_topo_over (l : list κ) (g : lgraph κ δ ε) : Prop :=
  l.is_topo_over g ∧ (∀ k : κ, k ∈ l ↔ k ∈ g)

namespace topo

  -- Complete topological orderings are permutations of each other.
  lemma complete_perm {g : lgraph κ δ ε} {l l' : list κ} (h : l.is_complete_topo_over g) (h' : l'.is_complete_topo_over g) :
    l ~ l' :=
    begin
      rw list.perm_ext h.left.left h'.left.left,
      intro x,
      unfold list.is_complete_topo_over at h h',
      rw [h.right x, h'.right x]
    end

  -- An item `k` is independent for a topological ordering if the corresponding graph contains no path
  -- that starts with an element in the ordering and ends in `k`.
  -- Note that `k` is not constrained to be an element of the topological ordering.
  def indep (k : κ) (t : list κ) (g : lgraph κ δ ε) : Prop := ∀ k' ∈ t, ¬(k'~g~>k)

  -- The head of a topological ordering is always independent.
  lemma indep_head (hd : κ) (tl : list κ) {g : lgraph κ δ ε} (h : (hd :: tl).is_topo_over g) :
    indep hd (hd :: tl) g :=
    begin
      unfold indep,
      unfold list.is_topo_over at h,
      intros x hₓ,
      by_contradiction hc,
      have hᵢ, from h.right x hd hₓ (list.mem_cons_self hd tl) hc,
      rw list.index_of_cons_self hd tl at hᵢ,
      exact nat.not_lt_zero _ hᵢ
    end

  -- If an element is independent in a list, then it is also independent in its tail.
  lemma indep_cons {k hd : κ} {tl : list κ} {g : lgraph κ δ ε} (h : indep k (hd :: tl) g) :
    indep k tl g :=
    begin
      unfold indep at h ⊢,
      intros x hₓ,
      exact h x (list.mem_cons_of_mem _ hₓ)
    end

  -- If an element is independent in a list, then if is also independent in a permutation of that list.
  lemma indep_perm {k : κ} {t t' : list κ} {g : lgraph κ δ ε} (hₚ : t ~ t') (hᵢ : indep k t g) :
    indep k t' g :=
    begin 
      unfold indep at hᵢ ⊢,
      intros x hₓ,
      have hₘ, from (list.perm.mem_iff hₚ).mpr hₓ,
      exact hᵢ x hₘ
    end

end topo