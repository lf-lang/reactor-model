import data.rel
import data.finset
open classical

-- Inspired by: https://gist.github.com/MonoidMusician/1c8cc2ec787ebaf91b95d67cbc5c3498

namespace split_digraph

  --! Use this at the level of reactions, not reactors.
  structure node (U S D : Type*) :=
    (unit : U)
    (src : S)
    (dst : D)
    (s_to_u : S → U)
    (d_to_u : D → U)

  def well_split {U S D : Type*} (nodes : finset (node U S D)) :=
    ∀ n n' : node U S D, (n ∈ nodes ∧ n' ∈ nodes) → 
      (n.unit = n'.unit) ∨ (n.src = n'.src) ∨ (n.dst = n'.dst) → n = n'

  theorem well_split_subset {U S D : Type*} {super : finset (node U S D)} (w : well_split super) (nodes : finset (node U S D)) (sub : nodes ⊆ super) : well_split nodes :=
    sorry

end split_digraph

open split_digraph

--! If U are reactions, then S and D are their
--! First insert every reactor's reaction, represented by (reactorIdx, reactionIdx) ∈ ℕ × ℕ (or fin × fin).
structure split_digraph (U S D : Type*) :=
  (nodes : finset (node U S D))
  (split : well_split nodes)
  (conns : rel S D) 

namespace split_digraph

  universes u v w
  variables {U : Type u} {S : Type v} {D : Type w}

  /-inductive path (g : split_digraph U S D) (u u' : U)
    | direct (n n' : node U S D) : (n ∈ g.nodes) → (n' ∈ g.nodes) → (n.unit = u) → (n'.unit = u') → (g.conns n.src n'.dst) → path
    | composit {uₘ : U} : (path /-u uₘ-/) → (path /-uₘ u'-/) → path-/

  inductive path (g : split_digraph U S D) : U → U → Type (max u v w)

  def path.direct {n n' : node U S D} (g : split_digraph U S D) : (g.conns n.src n'.dst) → path g n.unit n'.unit
  def path.composite {n nₘ n' : node U S D} (g : split_digraph U S D) : (g.conns n.src nₘ.dst) → (path g nₘ.unit n'.unit) → path g n.unit n'.unit

  -- If there is a path from u u', they can not be the same.
  def is_acyclic (g : split_digraph U S D) := 
    ∀ (u u' : U), path g u u' → u ≠ u'

  def is_input_unique (g : split_digraph U S D) :=
    ∀ (s₁ s₂ : S) (d : D), (g.conns s₁ d) ∧ (g.conns s₂ d) → s₁ = s₂

  private def has_no_in (g : split_digraph U S D) (n : node U S D) := 
    ∃ s : S, g.conns s n.dst

  instance (g : split_digraph U S D) : decidable_pred (has_no_in g) := sorry

  private def no_ins (g : split_digraph U S D) : finset (node U S D) :=
    g.nodes.filter (has_no_in g)

  private def true_pred {α : Type*} (a a' : α) := true
  instance {α : Type} : is_trans α true_pred := sorry
  instance {α : Type} : is_antisymm α true_pred := sorry
  instance {α : Type} : is_total α true_pred := sorry
  instance {α : Type} : decidable_rel (@true_pred α) := sorry

  -- https://github.com/leanprover-community/mathlib/blob/a9fb069baa9e7c6816995feb9e93657b94539e4e/src/data/finset/basic.lean#L747
  instance {α : Type} : has_sdiff (finset α) := sorry

  instance : decidable_eq (node U S D) := sorry

  --! Define topo_sort as the predicate of what it means.
  --> Show that det. holds for reactors as long as alg. produces topol. sort. No matter which one.

  -- https://courses.cs.washington.edu/courses/cse326/03wi/lectures/RaoLect20.pdf
  private def topo_order' (g : split_digraph U S D) (acc : list (node U S D)) : (split_digraph U S D) × list (node U S D) :=
    if g.nodes = ∅ then
      ⟨g, acc⟩
    else 
      let αs := no_ins g in
      let αlist := αs.sort true_pred in -- This is simply supposed to flatten the set into a list.
      let acc' := acc ++ αlist in
      let nodes' := g.nodes \ αs in
      let nodes'_split := well_split_subset g.split nodes' (finset.sdiff_subset g.nodes αs) in
      let g' : split_digraph U S D := ⟨nodes', nodes'_split, g.conns⟩ in
      topo_order' g' acc

  
  def topo_order (g : split_digraph U S D) : list U := (topo_order' g []).2.map node.unit

end split_digraph