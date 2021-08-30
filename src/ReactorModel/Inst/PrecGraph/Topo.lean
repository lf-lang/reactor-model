import ReactorModel.Inst.PrecGraph.Path

variable {ι υ} [ID ι] [Value υ] {η : Network ι υ}

-- The definition of what it means for a given list to be a topological ordering for a given graph.
-- Note that this is not the same as a "complete" topological ordering (`list.is_complete_topo_over`).
-- 
-- `list`s with `nodup` are the formalization for finite ordered sets: 
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Ordered.20set
def List.isTopoOver (l : List ι) (π : PrecGraph η) : Prop :=
  l.nodup ∧ (∀ rcn₁ rcn₂, rcn₁ ∈ l → rcn₂ ∈ l → (rcn₁ ~π~> rcn₂) → (l.indexOf rcn₁ < l.indexOf rcn₂))

namespace Topo

-- Removing an element from a topological ordering does not break the property of it being a topological ordering.
theorem eraseIsTopo {t : List ι} {π : PrecGraph η} (rcn : ι) (h : t.isTopoOver π) :
  (t.erase rcn).isTopoOver π := by
  simp only [List.isTopoOver] at h ⊢
  split
  case left => exact List.nodup_erase_of_nodup _ h.left
  case right =>
    intros x x' hₓ hₓ' hₚ
    have hᵢ := h.right x x' (List.mem_of_mem_erase hₓ) (List.mem_of_mem_erase hₓ') hₚ
    exact List.index_of_erase_lt hᵢ hₓ hₓ' h.left

-- If a list is a topological ordering for some graph, then so is its tail.
theorem consIsTopo {hd : ι} {tl : List ι} {π : PrecGraph η} (h : (hd :: tl).isTopoOver π) :
  tl.isTopoOver π := by
  rw [←List.erase_cons_head hd tl]
  exact eraseIsTopo hd h

end Topo

-- A topological ordering is "complete" if it contains all of its graph's vertices.
def List.isCompleteTopoOver (l : List ι) (π : PrecGraph η) : Prop :=
  l.isTopoOver π ∧ (∀ rcn, rcn ∈ l ↔ rcn ∈ π.rcns.ids)

namespace Topo

-- Complete topological orderings are permutations of each other.
theorem completePerm {π : PrecGraph η} {l l' : List ι} (h : l.isCompleteTopoOver π) (h' : l'.isCompleteTopoOver π) :
  l ~ l' := by
  rw [List.perm_ext h.left.left h'.left.left]
  intro x
  simp only [List.isCompleteTopoOver] at h h'
  rw [h.right x, h'.right x]

-- An item `rcn` is independent in a topological ordering if the corresponding graph contains no path
-- that starts with an element in the ordering and ends in `rcn`.
-- Note that `rcn` is not constrained to be an element of the topological ordering.
def indep (rcn₁ : ι) (t : List ι) (π : PrecGraph η) : Prop := ∀ rcn₂ ∈ t, ¬(rcn₂ ~π~> rcn₁)

-- The head of a topological ordering is always independent.
theorem indepHead (hd : ι) (tl : List ι) {π : PrecGraph η} (h : (hd :: tl).isTopoOver π) :
  indep hd (hd :: tl) π := by
  simp only [indep]
  simp only [List.isTopoOver] at h
  intros x hₓ
  byContra hc
  have hᵢ := h.right x hd hₓ (List.mem_cons_self hd tl) hc
  rw [List.index_of_cons_self hd tl] at hᵢ
  exact Nat.not_lt_zero _ hᵢ

-- If an element is independent in a list, then it is also independent in its tail.
theorem indepCons {rcn hd : ι} {tl : List ι} {π : PrecGraph η} (h : indep rcn (hd :: tl) π) :
  indep rcn tl π := by
  simp only [indep] at h ⊢
  intros x hₓ
  exact h x (List.mem_cons_of_mem _ hₓ)

-- If an element is independent in a list, then if is also independent in a permutation of that list.
theorem indepPerm {rcn : ι} {t t' : List ι} {π : PrecGraph η} (hₚ : t ~ t') (hᵢ : indep rcn t π) :
  indep rcn t' π := by 
  simp only [indep] at hᵢ ⊢
  intros x hₓ
  have hₘ := (List.perm.mem_iff hₚ).mpr hₓ
  exact hᵢ x hₘ

end Topo