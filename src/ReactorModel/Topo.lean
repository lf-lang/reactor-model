import ReactorModel.LGraph

variable {κ δ ε : Type _}
variable [DecidableEq κ] [DecidableEq δ] [LGraph.Edge ε κ]

-- The definition of what it means for a given list to be a topological ordering for a given graph.
-- Note that this is not the same as a "complete" topological ordering (`list.is_complete_topo_over`).
-- 
-- `list`s with `nodup` are the formalization for finite ordered sets: 
-- https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/Ordered.20set
def List.isTopoOver (l : List κ) (g : LGraph κ δ ε) : Prop :=
  l.nodup ∧ (∀ k k', k ∈ l → (k' ∈ l) → (k~g~>k') → (l.indexOf k < l.indexOf k'))

namespace Topo

-- Removing an element from a topological ordering does not break the property of it being a topological ordering.
theorem eraseIsTopo {t : List κ} {g : LGraph κ δ ε} (k : κ) (h : t.isTopoOver g) :
  (t.erase k).isTopoOver g := by
  simp only [List.isTopoOver] at h ⊢
  split
  focus
    exact List.nodup_erase_of_nodup _ h.left
  focus
    intros x x' hₓ hₓ' hₚ
    have hᵢ := h.right x x' (List.mem_of_mem_erase hₓ) (List.mem_of_mem_erase hₓ') hₚ
    exact List.index_of_erase_lt hᵢ hₓ hₓ' h.left

-- If a list is a topological ordering for some graph, then so is its tail.
theorem consIsTopo {hd : κ} {tl : List κ} {g : LGraph κ δ ε} (h : (hd :: tl).isTopoOver g) :
  tl.isTopoOver g := by
  rw [←List.erase_cons_head hd tl]
  exact eraseIsTopo hd h

end Topo

-- A topological ordering is "complete" if it contains all of its graph's vertices.
def List.isCompleteTopoOver (l : List κ) (g : LGraph κ δ ε) : Prop :=
  l.isTopoOver g ∧ (∀ k : κ, k ∈ l ↔ k ∈ g.keys) -- The `.keys` should be redundant here, but the Mem-instance cant be synthed atm ¯\_(ツ)_/¯ 

namespace Topo

-- Complete topological orderings are permutations of each other.
theorem completePerm {g : LGraph κ δ ε} {l l' : List κ} (h : l.isCompleteTopoOver g) (h' : l'.isCompleteTopoOver g) :
  l ~ l' := by
  rw [List.perm_ext h.left.left h'.left.left]
  intro x
  simp only [List.isCompleteTopoOver] at h h'
  rw [h.right x, h'.right x]

-- An item `k` is independent for a topological ordering if the corresponding graph contains no path
-- that starts with an element in the ordering and ends in `k`.
-- Note that `k` is not constrained to be an element of the topological ordering.
def indep (k : κ) (t : List κ) (g : LGraph κ δ ε) : Prop := ∀ k' ∈ t, ¬(k'~g~>k)

-- The head of a topological ordering is always independent.
theorem indepHead (hd : κ) (tl : List κ) {g : LGraph κ δ ε} (h : (hd :: tl).isTopoOver g) :
  indep hd (hd :: tl) g := by
  simp only [indep]
  simp only [List.isTopoOver] at h
  intros x hₓ
  byContra hc
  have hᵢ := h.right x hd hₓ (List.mem_cons_self hd tl) hc
  rw [List.index_of_cons_self hd tl] at hᵢ
  exact Nat.not_lt_zero _ hᵢ

-- If an element is independent in a list, then it is also independent in its tail.
theorem indepCons {k hd : κ} {tl : List κ} {g : LGraph κ δ ε} (h : indep k (hd :: tl) g) :
  indep k tl g := by
  simp only [indep] at h ⊢
  intros x hₓ
  exact h x (List.mem_cons_of_mem _ hₓ)

-- If an element is independent in a list, then if is also independent in a permutation of that list.
theorem indepPerm {k : κ} {t t' : List κ} {g : LGraph κ δ ε} (hₚ : t ~ t') (hᵢ : indep k t g) :
  indep k t' g := by 
  simp only [indep] at hᵢ ⊢
  intros x hₓ
  have hₘ := (List.perm.mem_iff hₚ).mpr hₓ
  exact hᵢ x hₘ

end Topo