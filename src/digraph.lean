import data.finset 

-- Associated discussion:
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Understanding.20Type.20Classes

-- Type `ε` is a `digraph.edge`-type over indices `ι`, if any instance of it can produce a `src`
-- and `dst` index.
class digraph.edge (ε ι : Type*) :=
  (src : ε → ι)
  (dst : ε → ι)

variables (ι δ ε : Type*)
variables [decidable_eq ι] [decidable_eq δ] [digraph.edge ε ι]

-- The proposition that a given set of edges makes connections only between given IDs.
def digraph.edges_are_formed_over_ids {ι ε} [digraph.edge ε ι] (edges : finset ε) (ids : finset ι) : Prop :=
  ∀ e ∈ edges, (digraph.edge.src e) ∈ ids ∧ (digraph.edge.dst e) ∈ ids

-- The vertices (of type `α`) have to have an associated index (of type `ι`), because otherwise it
-- wouldn't be possible to have multiple instances of the same reactor in a network.
-- Multisets are not enough, because then their edges can't be distinguished from one another.
--
-- A previous approach defined the nodes and indices together, as `ι → δ`. The nice thing about
-- this was that all indices of type `ι` were guaranteed to reference a vertex in the graph. The
-- problem with this though, is that you can't remove/add a vertex from/to the graph without
-- changing the underlying index-type `ι`. Hence the current approach which uses a `finset ι` is
-- used, so `ι` can stay the same. An inconvenience that arises as a result of this more flexible
-- approach is that functions over indices might have to require `(i : { x // x ∈ g.ids})` as
-- parameter instead of just `(i : ι)`.
@[ext] -- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/How.20to.20prove.20.20equality.20of.20structure/near/202105252
structure digraph :=
  (ids : finset ι)
  (data : ι → δ)
  (edges : finset ε)
  (validity : digraph.edges_are_formed_over_ids edges ids)

namespace digraph

  variables {ι δ ε}

  instance i_mem : has_mem ι (digraph ι δ ε) := {mem := λ i g, i ∈ g.ids}
  instance d_mem : has_mem δ (digraph ι δ ε) := {mem := λ d g, ∃ i, g.data i = d}
  instance e_mem : has_mem ε (digraph ι δ ε) := {mem := λ e g, e ∈ g.edges}

  -- The data elements contained in a given digraph.
  def members (g : digraph ι δ ε) : finset δ :=
    g.ids.image g.data

  -- Produces a graph where the member at a given ID `i` is replaced by a new member `d`.
  def update_data (g : digraph ι δ ε) (i : ι) (d : δ) : digraph ι δ ε :=
    {digraph . data := function.update g.data i d, ..g} 

  -- The proposition that a given digraph connects two given vertices with an edge.
  def has_edge_from_to (g : digraph ι δ ε) (i i' : ι) : Prop :=
    ∃ e ∈ g.edges, (edge.src e, edge.dst e) = (i, i')

  notation i-g->i' := g.has_edge_from_to i i'

  -- The proposition that a given digraph connects two given vertices by some path.
  inductive has_path_from_to (g : digraph ι δ ε) : ι → ι → Prop
    | direct {i i' : ι} : (i-g->i') → has_path_from_to i i'
    | composite {i iₘ i' : ι} : has_path_from_to i iₘ → has_path_from_to iₘ i' → has_path_from_to i i'

  notation i~g~>i' := g.has_path_from_to i i'

  -- The proposition that a given digraph is acyclic.
  def is_acyclic (g : digraph ι δ ε) : Prop := 
    ∀ i, ¬ i~g~>i

  variable [decidable_eq ι]

  -- The definition of what it means for a given list to be a topological order wrt a given DAG.
  def is_topological_order (l : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) : Prop :=
    ∀ i i' ∈ l, (i~g~>i') → (l.index_of i < l.index_of i')

  def is_complete_topo_over (l : list ι) (g : digraph ι δ ε) (h : g.is_acyclic) : Prop :=
    is_topological_order l h ∧ ∀ i : ι, i ∈ l ↔ i ∈ g  

  -- An item `i` in a topo list is fully independent if the corresponding graph contains no path
  -- that starts with an element in the topo and ends in `i`.
  def fully_indep (i : ι) (t : list ι) (g : digraph ι δ ε) : Prop :=
    ∀ i' ∈ t, ¬(i'~g~>i)

  lemma topo_head_fully_indep (hd : ι) (tl : list ι) {g : digraph ι δ ε} (h_a : g.is_acyclic) (h_t : is_topological_order (hd :: tl) h_a) :
    fully_indep hd (hd :: tl) g :=
    sorry

  lemma fully_indep_perm (i : ι) {t t' : list ι} {g : digraph ι δ ε} (h_a : g.is_acyclic) (h_t : is_topological_order t h_a) (h_t' : is_topological_order t' h_a) :
    t ~ t' → fully_indep i t g → fully_indep i t' g :=
    sorry

  -- For any DAG there exists a list which is a topological order of the DAG.
  theorem any_dag_has_complete_topo : 
    ∀ (g : digraph ι δ ε) (h : g.is_acyclic), ∃ l : list ι, is_complete_topo_over l g h :=
    sorry
    -- https://ocw.tudelft.nl/wp-content/uploads/Algoritmiek_DAGs_and_Topological_Ordering.pdf
    -- Lemma 3.20

  lemma topo_cons (hd : ι) (tl : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) :
    is_topological_order (hd :: tl) h → is_topological_order tl h :=
    begin
      intro hₜ,
      unfold is_topological_order at hₜ ⊢,
      intros i i' hᵢ hᵢ' hₚ,
      have hₜ', from hₜ i i' (list.mem_cons_of_mem _ hᵢ) (list.mem_cons_of_mem _ hᵢ') hₚ,
      repeat { rw list.index_of_cons at hₜ' },
      sorry
    end

  -- Removing an element from a topological order still keeps it topo.
  lemma topo_erase (i : ι) (t : list ι) {g : digraph ι δ ε} (h : g.is_acyclic) :
    is_topological_order t h → is_topological_order (t.erase i) h :=
    begin
      sorry
    end

  lemma topo_no_dup {g : digraph ι δ ε} {hₐ : g.is_acyclic} {l : list ι} :
    is_topological_order l hₐ → l.nodup :=
    begin
      intro h,
      sorry
    end

  lemma complete_topos_are_perm {g : digraph ι δ ε} {hₐ : g.is_acyclic} {l l' : list ι} :
    is_complete_topo_over l g hₐ → is_complete_topo_over l' g hₐ → l ~ l' :=
    begin
      intros h h', 
      suffices hₚ : ∀ x (y : is_complete_topo_over x g hₐ), x ~ g.ids.val.to_list,
      from list.perm.trans (hₚ l h) (list.perm.symm (hₚ l' h')),
      intros x y,
      rw list.perm_ext (topo_no_dup y.left) sorry,
      intro i,
      rw multiset.mem_to_list,
      exact y.right i,
    end

  lemma update_data_comm {i i' : ι} (h : i ≠ i') (d d' : δ) (g : digraph ι δ ε) :
    (g.update_data i d).update_data i' d' = (g.update_data i' d').update_data i d :=
    begin
      unfold update_data,
      rw function.update_comm,
      exact h,
    end

  lemma edges_inv_path_inv {g g' : digraph ι δ ε} {i i' : ι} (h : g.edges = g'.edges) :
    (i~g~>i') → (i~g'~>i') :=
    begin
      intros h,
      induction h with _ _ p _ _ _ p_α p_ω p_α' p_ω',
        {
          rw [has_edge_from_to, h] at p,
          exact has_path_from_to.direct p
        },
        exact has_path_from_to.composite p_α' p_ω'
    end

  lemma edges_inv_acyclic_inv {g g' : digraph ι δ ε} :
    g.edges = g'.edges → g.is_acyclic → g'.is_acyclic :=
    begin
      intros hₑ hₐ,
      unfold is_acyclic,
      intro i,
      by_contradiction h_f,
      have h_c, from edges_inv_path_inv (symm hₑ) h_f,
      have : ¬(i~g~>i), from hₐ i,
      contradiction
    end

  lemma update_data_is_ids_inv (g : digraph ι δ ε) :
    ∀ i d, (g.update_data i d).ids = g.ids :=
    by finish

  lemma update_data_is_edges_inv (g : digraph ι δ ε) :
    ∀ i d, (g.update_data i d).edges = g.edges :=
    by finish

end digraph 
