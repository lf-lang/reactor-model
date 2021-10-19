import ReactorModel.Inst.PrecGraph.Path

variable {ι υ} [ID ι] [Value υ] {σ : Reactor ι υ}

-- The definition of what it means for a given list to be a topological ordering for a given precedence graph.
-- Note that this is not the same as a "complete" topological ordering (`list.is_complete_topo_over`).
-- 
-- `List`s with `nodup` are the formalization for finite ordered sets: 
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Ordered.20set
structure List.isTopoOver (l : List ι) (π : PrecGraph σ) : Prop where
  nodup : l.nodup 
  mem   : ∀ {rcn}, (rcn ∈ l) → (rcn ∈ π.rcns.ids)
  order : ∀ {rcn₁ rcn₂}, (rcn₁ ∈ l) → (rcn₂ ∈ l) → (rcn₁ ~[π]~> rcn₂) → (l.indexOf rcn₁ < l.indexOf rcn₂)

namespace Topo

-- Removing an element from a topological ordering does not break the property of it being a topological ordering.
theorem eraseIsTopo {t : List ι} {π : PrecGraph σ} (rcn : ι) (h : t.isTopoOver π) :
  (t.erase rcn).isTopoOver π := {
    nodup := List.nodup_erase_of_nodup _ h.nodup,
    mem := λ hₓ => h.mem (List.mem_of_mem_erase hₓ),
    order := by
      intro x x' hₓ hₓ' hₚ
      have hᵢ := h.order (List.mem_of_mem_erase hₓ) (List.mem_of_mem_erase hₓ') hₚ
      exact List.index_of_erase_lt hᵢ hₓ hₓ' h.nodup
  }

-- If a list is a topological ordering for some graph, then so is its tail.
theorem consIsTopo {hd : ι} {tl : List ι} {π : PrecGraph σ} (h : (hd :: tl).isTopoOver π) :
  tl.isTopoOver π := by
  rw [←List.erase_cons_head hd tl]
  exact eraseIsTopo hd h

end Topo

-- A topological ordering is "complete" if it contains all of its graph's vertices.
structure List.isCompleteTopoOver (l : List ι) (π : PrecGraph σ) extends List.isTopoOver l π : Prop where
  complete : ∀ rcn, rcn ∈ l ↔ rcn ∈ π.rcns.ids

namespace Topo

-- Complete topological orderings are permutations of each other.
theorem completePerm {π : PrecGraph σ} {l l' : List ι} (h : l.isCompleteTopoOver π) (h' : l'.isCompleteTopoOver π) :
  l ~ l' := by
  rw [List.perm_ext h.nodup h'.nodup]
  intro x
  rw [h.complete x, h'.complete x]

-- An item `rcn` is independent in a topological ordering if the corresponding graph contains
-- no path that starts with an element in the ordering and ends in `rcn`.
-- 
-- Note that `rcn` *is* constrained to be an element in the precedence graph, but *not*
-- to be an element of the topological ordering.
protected structure indep (rcn : ι) (t : List ι) (π : PrecGraph σ) : Prop where
  mem  : rcn ∈ π.rcns.ids
  path : ∀ rcn' ∈ t, ¬(rcn' ~[π]~> rcn)

-- The head of a topological ordering is always independent.
theorem indepHead (hd : ι) (tl : List ι) {π : PrecGraph σ} (h : (hd :: tl).isTopoOver π) :
  Topo.indep hd (hd :: tl) π := {
    mem := h.mem (List.mem_cons_self hd tl),
    path := by
      intros x hₓ
      byContra hc
      have hᵢ := h.order hₓ (List.mem_cons_self hd tl) hc
      rw [List.index_of_cons_self hd tl] at hᵢ
      exact Nat.not_lt_zero _ hᵢ
  }

-- If an element is independent in a list, then it is also independent in its tail.
theorem indepCons {rcn hd : ι} {tl : List ι} {π : PrecGraph σ} (h : Topo.indep rcn (hd :: tl) π) :
  Topo.indep rcn tl π := {
    mem := h.mem,
    path := λ x hₓ => h.path x (List.mem_cons_of_mem _ hₓ)
  }

-- If an element is independent in a list, then if is also independent in a permutation of that list.
theorem indepPerm {rcn : ι} {t t' : List ι} {π : PrecGraph σ} (hₚ : t ~ t') (hᵢ : Topo.indep rcn t π) :
  Topo.indep rcn t' π := {
    mem := hᵢ.mem,
    path := λ x hₓ => hᵢ.path x ((List.perm.mem_iff hₚ).mpr hₓ)
  }

end Topo