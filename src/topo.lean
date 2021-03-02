import digraph
import mathlib

variables {ι δ ε : Type*}
variables [decidable_eq ι] [decidable_eq δ] [digraph.edge ε ι]

-- The definition of what it means for a given list to be a topological ordering for a given graph.
-- Note that this is not the same as a "complete" topological ordering (`list.is_complete_topo_over`).
def list.is_topo_over (l : list ι) (g : digraph ι δ ε) : Prop :=
  l.nodup ∧ ∀ i i' ∈ l, (i~g~>i') → (l.index_of i < l.index_of i')

namespace topo

  -- Removing an element from a topological ordering does not break the property of it being a topological ordering.
  lemma topo_erase (i : ι) {t : list ι} {g : digraph ι δ ε} (h : t.is_topo_over g) :
    (t.erase i).is_topo_over g :=
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
  lemma topo_cons {hd : ι} {tl : list ι} {g : digraph ι δ ε} (h : (hd :: tl).is_topo_over g) :
    tl.is_topo_over g :=
    begin
      rw ←list.erase_cons_head hd tl,
      exact topo_erase hd h
    end

end topo

-- A topological ordering is "complete" if it contains all of its graph's vertices.
def list.is_complete_topo_over (l : list ι) (g : digraph ι δ ε) : Prop :=
  l.is_topo_over g ∧ ∀ i : ι, i ∈ l ↔ i ∈ g  

namespace topo

  -- For any acyclic digraph there exists a complete topological ordering of that graph.
  -- https://ocw.tudelft.nl/wp-content/uploads/Algoritmiek_DAGs_and_Topological_Ordering.pdf
  -- Lemma 3.20
  theorem any_dag_has_complete_topo : 
    ∀ (g : digraph ι δ ε) (h : g.is_acyclic), ∃ l : list ι, l.is_complete_topo_over g := 
    sorry

  -- Complete topological orderings are permutations of each other.
  lemma complete_perm {g : digraph ι δ ε} {l l' : list ι} (h : l.is_complete_topo_over g) (h' : l'.is_complete_topo_over g) :
    l ~ l' :=
    begin
      rw list.perm_ext h.left.left h'.left.left,
      intro x,
      unfold list.is_complete_topo_over at h h',
      rw [h.right x, h'.right x]
    end

  -- An item `i` in a topological ordering is independent if the corresponding graph contains no path
  -- that starts with an element in the ordering and ends in `i`.
  def indep (i : ι) (t : list ι) (g : digraph ι δ ε) : Prop :=
    ∀ i' ∈ t, ¬(i'~g~>i)

  -- The head of a topological ordering is always independent.
  lemma indep_head (hd : ι) (tl : list ι) {g : digraph ι δ ε} (h : (hd :: tl).is_topo_over g) :
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
  lemma indep_cons {i hd : ι} {tl : list ι} {g : digraph ι δ ε} (h : indep i (hd :: tl) g) :
    indep i tl g :=
    begin
      unfold indep at h ⊢,
      intros x hₓ,
      exact h x (list.mem_cons_of_mem _ hₓ)
    end

  -- If an element is independent in a list, then if is also independent in a permutation of that list.
  lemma indep_perm {i : ι} {t t' : list ι} {g : digraph ι δ ε} (hₚ : t ~ t') (hᵢ : indep i t g) :
    indep i t' g :=
    begin 
      unfold indep at hᵢ ⊢,
      intros x hₓ,
      have hₘ, from (list.perm.mem_iff hₚ).mpr hₓ,
      exact hᵢ x hₘ
    end

end topo