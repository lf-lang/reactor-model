import digraph

variables {ι δ ε : Type*}
variables [decidable_eq ι] [decidable_eq δ] [digraph.edge ε ι]

-- The definition of what it means for a given list to be a topological order wrt a given DAG.
def list.is_topological_order (l : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) : Prop :=
  ∀ i i' ∈ l, (i~g~>i') → (l.index_of i < l.index_of i')

def list.is_complete_topo (l : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) : Prop :=
  l.is_topological_order h ∧ ∀ i : ι, i ∈ l ↔ i ∈ g  

namespace topo

  -- An item `i` in a topo list is fully independent if the corresponding graph contains no path
  -- that starts with an element in the topo and ends in `i`.
  def fully_indep (i : ι) (t : list ι) (g : digraph ι δ ε) : Prop :=
    ∀ i' ∈ t, ¬(i'~g~>i)

  lemma topo_head_fully_indep (hd : ι) (tl : list ι) {g : digraph ι δ ε} (h_a : g.is_acyclic) (h_t : (hd :: tl).is_topological_order h_a) :
    fully_indep hd (hd :: tl) g :=
    sorry

  lemma topo_fully_indep_cons (i hd : ι) (tl : list ι) {g : digraph ι δ ε} (h_a : g.is_acyclic) (h_t : (hd :: tl).is_topological_order h_a) :
    fully_indep i (hd :: tl) g → fully_indep i tl g :=
    sorry

  lemma fully_indep_perm (i : ι) {t t' : list ι} {g : digraph ι δ ε} (h_a : g.is_acyclic) (h_t : t.is_topological_order h_a) (h_t' : t'.is_topological_order h_a) :
    t ~ t' → fully_indep i t g → fully_indep i t' g :=
    sorry

  -- For any DAG there exists a list which is a topological order of the DAG.
  theorem any_dag_has_complete_topo : 
    ∀ (g : digraph ι δ ε) (h : g.is_acyclic), ∃ l : list ι, l.is_complete_topo h :=
    sorry
    -- https://ocw.tudelft.nl/wp-content/uploads/Algoritmiek_DAGs_and_Topological_Ordering.pdf
    -- Lemma 3.20

  lemma topo_cons (hd : ι) (tl : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) :
    (hd :: tl).is_topological_order h → tl.is_topological_order h :=
    begin
      intro hₜ,
      unfold list.is_topological_order at hₜ ⊢,
      intros i i' hᵢ hᵢ' hₚ,
      have hₜ', from hₜ i i' (list.mem_cons_of_mem _ hᵢ) (list.mem_cons_of_mem _ hᵢ') hₚ,
      repeat { rw list.index_of_cons at hₜ' },
      sorry
    end

  -- Removing an element from a topological order still keeps it topo.
  lemma topo_erase (i : ι) (t : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) :
    t.is_topological_order h → (t.erase i).is_topological_order h :=
    begin
      sorry
    end

  lemma topo_no_dup {g : digraph ι δ ε} {hₐ : g.is_acyclic} {l : list ι} :
    l.is_topological_order hₐ → l.nodup :=
    begin
      intro h,
      sorry
    end

  lemma complete_topos_are_perm {g : digraph ι δ ε} {hₐ : g.is_acyclic} {l l' : list ι} :
    l.is_complete_topo hₐ → l'.is_complete_topo hₐ → l ~ l' :=
    begin
      intros h h', 
      suffices hₚ : ∀ (x : list _) (y : x.is_complete_topo hₐ), x ~ g.ids.val.to_list,
      from list.perm.trans (hₚ l h) (list.perm.symm (hₚ l' h')),
      intros x y,
      rw list.perm_ext (topo_no_dup y.left) sorry,
      intro i,
      rw multiset.mem_to_list,
      exact y.right i,
    end

end topo