import ReactorModel.Execution

open Classical ReactorType

theorem ReactorType.Wellformed.rcn_state_deps_local {rtr : Reactor}
    (hc₁ : rtr[.rtr][c₁] = some con₁) (hc₂ : rtr[.rtr][c₂] = some con₂) 
    (hr₁ : con₁.rcns i₁ = some rcn₁) (hr₂ : con₂.rcns i₂ = some rcn₂)
    (hd₁ : ⟨.stv, j⟩ ∈ rcn₁.deps k₁) (hd₂ : ⟨.stv, j⟩ ∈ rcn₂.deps k₂) : c₁ = c₂ := by
  have hv₁ := rtr.wellformed.valid_deps hc₁ hr₁ hd₁
  have hv₂ := rtr.wellformed.valid_deps hc₂ hr₂ hd₂
  cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> simp [hk₁, hk₂] at hv₁ hv₂
  all_goals 
    cases hv₁; cases hv₂
    exact Indexable.mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .stv) ‹_› ‹_› 

-- This proposition states that `rcn₂` does not depend on `rcn₁`.
abbrev NotDependent (rtr : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ <[rtr] rcn₂)

notation:50 rcn₁ " ≮[" rtr "] " rcn₂ => NotDependent rtr rcn₁ rcn₂

variable {rtr : Reactor}

theorem NotDependent.deps_disjoint {d} (hi : i₁ ≮[rtr] i₂) (h₁ : rtr[.rcn][i₁] = some rcn₁)
    (h₂ : rtr[.rcn][i₂] = some rcn₂) (h : d ∈ rcn₁.deps .out) (hs : d.cpt ≠ .stv) : 
    d ∉ rcn₂.deps .in :=
  byContradiction fun hd => absurd (Dependency.depOverlap h₁ h₂ h (not_not.mp hd) hs) hi

structure Independent (rtr : Reactor) (rcn₁ rcn₂ : ID) : Prop where
  not_eq : rcn₁ ≠ rcn₂  
  left   : rcn₁ ≮[rtr] rcn₂
  right  : rcn₂ ≮[rtr] rcn₁

namespace Independent

notation:50 rcn₁ " ≮[" rtr "]≯ " rcn₂ => Independent rtr rcn₁ rcn₂

theorem symm (hi : i₁ ≮[rtr]≯ i₂) : i₂ ≮[rtr]≯ i₁ where
  not_eq := hi.not_eq.symm
  left   := hi.right
  right  := hi.left

theorem ne_con_state_mem_rcn₁_deps_not_mem_rcn₂_deps
    (hc : rtr[.rtr][c] = some con) (hr₁ : con.rcns i₁ = some rcn₁) (hr₂ : con.rcns i₂ = some rcn₂) 
    (hd : ⟨.stv, j⟩ ∈ rcn₁.deps .out) (hi : i₁ ≮[rtr]≯ i₂) (hs : .stv j v ∈ rcn₁ i) : 
    ⟨.stv, j⟩ ∉ rcn₂.deps k := by
  by_contra hd'
  have ⟨hn, _, _⟩ := hi 
  -- TODO: https://leanprover.zulipchat.com/#narrow/stream/348111-std4/topic/by_cases.20tags.20bug/near/345415921
  by_cases hm₁ : rcn₁.Mutates <;> by_cases hm₂ : rcn₂.Mutates
  rotate_left
  case _ => 
    have := Dependency.mutNorm hc ‹_› ‹_› hm₁ (by simp_all [Reaction.Mutates])
    contradiction
  case _ => 
    have := Dependency.mutNorm hc ‹_› hr₁ hm₂ (by simp_all [Reaction.Mutates])
    contradiction
  all_goals
    cases rtr.wellformed.hazards_prio hc hr₁ hr₂ hn hd hd' (.inl rfl)
    all_goals
      case _ hp =>
      have := Dependency.prio hc ‹_› ‹_› (by simp [*]) hp   
      contradiction
    
open Indexable in
theorem state_mem_rcn₁_deps_not_mem_rcn₂_deps 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂)
    (hi : i₁ ≮[rtr]≯ i₂) (hs : .stv j v ∈ rcn₁.body i) : ⟨.stv, j⟩ ∉ rcn₂.deps k := by
  have ⟨c₁, _, hc₁, hr₁⟩ := obj?_split h₁ 
  have ⟨c₂, _, hc₂, hr₂⟩ := obj?_split h₂ 
  have hd₁ := rcn₁.target_mem_deps hs
  simp [Change.Normal.target] at hd₁
  by_cases hc : c₁ = c₂
  case neg => 
    by_contra hd₂
    exact absurd (ReactorType.Wellformed.rcn_state_deps_local hc₁ hc₂ hr₁ hr₂ hd₁ hd₂) hc
  case pos => 
    injection hc₂ ▸ hc ▸ hc₁ with h
    exact ne_con_state_mem_rcn₁_deps_not_mem_rcn₂_deps hc₁ hr₁ (h ▸ hr₂) hd₁ hi hs

end Independent

-- Reaction `rcn` is maximal wrt. `rcns` if `rcn` does not depend on any reaction in `rcns`.
def Minimal (rtr : Reactor) (rcns : List ID) (rcn : ID) : Prop :=
  ∀ i ∈ rcns, i ≮[rtr] rcn

namespace Minimal

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