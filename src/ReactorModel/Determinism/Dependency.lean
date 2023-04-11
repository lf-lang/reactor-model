import ReactorModel.Execution

open Classical ReactorType Indexable

namespace Dependency

variable [Proper α] {rtr : α}

theorem same_con_needOrderedPriority
    (hc : rtr[.rtr][c] = some con) (h₁ : con{.rcn}{i₁} = some rcn₁) (h₂ : con{.rcn}{i₂} = some rcn₂) 
    (hn : i₁ ≠ i₂) (hp : Wellformed.NeedOrderedPriority rcn₁ rcn₂) : 
    (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) := by
  by_cases hm₁ : rcn₁.Mutates <;> by_cases hm₂ : rcn₂.Mutates
  rotate_left
  · exact .inl $ .mutNorm hc h₁ h₂ hm₁ (by simp_all [Reaction.Mutates])
  · exact .inr $ .mutNorm hc h₂ h₁ hm₂ (by simp_all [Reaction.Mutates])
  all_goals
    cases Proper.wellformed rtr |>.ordered_prio hc h₁ h₂ hn hp
    · exact .inr $ .prio hc h₂ h₁ (by simp_all) ‹_›
    · exact .inl $ .prio hc h₁ h₂ (by simp_all) ‹_›

theorem hazard 
    (hc : rtr[.rtr][c] = some con) (h₁ : con{.rcn}{i₁} = some rcn₁) (h₂ : con{.rcn}{i₂} = some rcn₂) 
    (hn : i₁ ≠ i₂) (hd₁ : ⟨.stv, i⟩ ∈ Reaction.deps rcn₁ k₁) 
    (hd₂ : ⟨.stv, i⟩ ∈ Reaction.deps rcn₂ k₂) (hk : k₁ = .out ∨ k₂ = .out) : 
    (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) := 
  same_con_needOrderedPriority hc h₁ h₂ hn (.hazard hd₁ hd₂ hk)

theorem same_con_shared_out_dep
    (hc : rtr[.rtr][c] = some con) (h₁ : con{.rcn}{i₁} = some rcn₁) (h₂ : con{.rcn}{i₂} = some rcn₂) 
    (hn : i₁ ≠ i₂) (hd₁ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₁ .out) 
    (hd₂ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₂ .out) : (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) :=
  same_con_needOrderedPriority hc h₁ h₂ hn (.overlap hd₁ hd₂)

theorem shared_out_dep
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (hn : i₁ ≠ i₂)
    (hd₁ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₁ .out) (hd₂ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₂ .out) :
    (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) := by  
  have ⟨_, _, hc₁, hr₁⟩ := obj?_some_split h₁
  have ⟨_, _, hc₂, hr₂⟩ := obj?_some_split h₂
  have hc := Proper.wellformed rtr |>.shared_dep_local hc₁ hc₂ hr₁ hr₂ hd₁ hd₂
  injection hc₂ ▸ hc ▸ hc₁ with hc
  exact same_con_shared_out_dep hc₁ hr₁ (hc ▸ hr₂) hn hd₁ hd₂

end Dependency

-- This proposition states that `rcn₂` does not depend on `rcn₁`.
abbrev NotDependent [Indexable α] (rtr : α) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ <[rtr] rcn₂)

namespace NotDependent

notation:50 rcn₁ " ≮[" rtr "] " rcn₂ => NotDependent rtr rcn₁ rcn₂

theorem equiv [Indexable α] {rtr₁ rtr₂ : α} (h : i₁ ≮[rtr₁] i₂) (e : rtr₁ ≈ rtr₂) : 
    i₁ ≮[rtr₂] i₂ :=
  (h $ ·.equiv e)

theorem deps_disjoint [Indexable α] {rtr : α} {d} (hi : i₁ ≮[rtr] i₂) 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (h : d ∈ rcn₁.deps .out) 
    (hs : d.cpt ≠ .stv) : d ∉ rcn₂.deps .in :=
  byContradiction fun hd => hi $ .depOverlap h₁ h₂ h (not_not.mp hd) hs

end NotDependent

structure Independent [Indexable α] (rtr : α) (rcn₁ rcn₂ : ID) : Prop where
  not_eq : rcn₁ ≠ rcn₂  
  left   : rcn₁ ≮[rtr] rcn₂
  right  : rcn₂ ≮[rtr] rcn₁

namespace Independent

notation:50 rcn₁ " ≮[" rtr "]≯ " rcn₂ => Independent rtr rcn₁ rcn₂

theorem symm [Indexable α] {rtr : α} (hi : i₁ ≮[rtr]≯ i₂) : i₂ ≮[rtr]≯ i₁ where
  not_eq := hi.not_eq.symm
  left   := hi.right
  right  := hi.left

theorem equiv [Indexable α] {rtr₁ rtr₂ : α} (hi : i₁ ≮[rtr₁]≯ i₂) (e : rtr₁ ≈ rtr₂) : 
    i₁ ≮[rtr₂]≯ i₂ where
  not_eq := hi.not_eq
  left   := hi.left.equiv e
  right  := hi.right.equiv e

theorem no_shared_state_deps [Proper α] {rtr : α}
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂)
    (hi : i₁ ≮[rtr]≯ i₂) (hs : .stv j v ∈ rcn₁.body i) : ⟨.stv, j⟩ ∉ rcn₂.deps k := by
  have hd₁ := rcn₁.target_mem_deps hs
  simp [Change.Normal.target] at hd₁
  by_contra hd₂
  have ⟨_, _, hc₁, hr₁⟩ := obj?_some_split h₁
  have ⟨_, _, hc₂, hr₂⟩ := obj?_some_split h₂
  have hc := Proper.wellformed rtr |>.shared_state_local hc₁ hc₂ hr₁ hr₂ hd₁ hd₂
  injection hc₂ ▸ hc ▸ hc₁ with hc
  cases Dependency.hazard hc₁ hr₁ (hc ▸ hr₂) hi.not_eq hd₁ hd₂ (.inl rfl) 
  all_goals simp [hi.left, hi.right] at *

end Independent

-- Reaction `rcn` is maximal wrt. `rcns` if `rcn` does not depend on any reaction in `rcns`.
def Minimal [Indexable α] (rtr : α) (rcns : List ID) (rcn : ID) : Prop :=
  ∀ i ∈ rcns, i ≮[rtr] rcn

namespace Minimal

variable [Indexable α] {rtr rtr₁ rtr₂ : α}

notation:50 rcns " ≮[" rtr "] " rcn => Minimal rtr rcns rcn

theorem cons_head (m : (hd :: tl) ≮[rtr] rcn) : hd ≮[rtr] rcn :=
  m hd $ List.mem_cons_self _ _

theorem cons_tail (m : (hd :: tl) ≮[rtr] rcn) : tl ≮[rtr] rcn :=
  (m · $ List.mem_cons_of_mem _ ·)

theorem perm {rcns : List ID} (m : rcns ≮[rtr] rcn) (h : rcns ~ rcns') : rcns' ≮[rtr] rcn :=
  (m · $ h.mem_iff.mpr ·)

theorem equiv {rcns : List ID} (m : rcns ≮[rtr₁] rcn) (e : rtr₁ ≈ rtr₂) : rcns ≮[rtr₂] rcn :=
  fun i h d => absurd (ReactorType.Dependency.equiv e d) (m i h)

end Minimal