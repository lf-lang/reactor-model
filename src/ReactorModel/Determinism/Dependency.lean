import ReactorModel.Execution

open Classical

-- This proposition states that `rcn₂` does not depend on `rcn₁`.
abbrev Independent (rtr : Reactor) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ <[rtr] rcn₂)

namespace Independent

notation:50 rcn₁ " ≮[" rtr "] " rcn₂ => Independent rtr rcn₁ rcn₂

theorem nonoverlapping_deps : 
  (i₁ ≮[σ] i₂) → (σ[.rcn][i₁] = some rcn₁) → (σ[.rcn][i₂] = some rcn₂) →
  (rcn₁.deps .out ∩ rcn₂.deps .in) = ∅ := by
  sorry -- exact absurd (ReactorType.Dependency.depOverlap ho₁ ho₂ $ Finset.nonempty_of_ne_empty hc) hi
 
theorem ne_con_or_pure {rcn₁ rcn₂ : rtr.Valid .rcn} (hi : rcn₁ ≮[rtr] rcn₂) (hn : rcn₁ ≠ rcn₂) :
    (rcn₁.con.id ≠ rcn₂.con.id) ∨ rcn₁.obj.Pure ∨ rcn₂.obj.Pure := by
  sorry
  /-intro h hn ho₁ ho₂ hc₁ hc₂ 
  by_contra hc
  have ⟨hc, hp⟩ := (not_or ..).mp hc
  simp [not_or] at hp hc
  have he := Reactor.con?_eq_id_to_eq hc₁ hc₂ hc
  simp [he] at hc₁
  have ⟨_, ho₁', hcm₁⟩ := Reactor.con?_to_obj?_and_cpt? hc₁
  have ⟨_, ho₂', hcm₂⟩ := Reactor.con?_to_obj?_and_cpt? hc₂
  have ho₁'' := ho₁'.symm.trans ho₁
  have ho₂'' := ho₂'.symm.trans ho₂
  simp [ho₁'', ho₂''] at hcm₁ hcm₂
  have hre := hc₂.trans hc₁.symm
  by_cases hm₁ : rcn₁.isMut 
  case pos =>
    by_cases hm₂ : rcn₂.isMut
    case pos =>
      cases c₂.obj.orderability (.muts hcm₁ hcm₂ hn hm₁ hm₂)
      case inl hpr =>
        have hd := Dependency.prio hre ho₂ ho₁ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.right 
      case inr hpr =>
        have hd := Dependency.prio hre.symm ho₁ ho₂ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.left 
    case neg => 
      have hd := Dependency.mutNorm hre.symm ho₁ ho₂ hm₁ (by simp_all [Reaction.isMut])
      exact absurd hd h.left 
  case neg =>
    by_cases hm₂ : rcn₂.isMut
    case pos =>
      have hd := Dependency.mutNorm hre ho₂ ho₁ hm₂ (by simp_all [Reaction.isMut])
      exact absurd hd h.right 
    case neg =>
      cases c₂.obj.orderability (.impure hcm₁ hcm₂ hn hp.left hp.right)
      case inl hpr =>
        have hd := Dependency.prio hre ho₂ ho₁ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.right 
      case inr hpr =>
        have hd := Dependency.prio hre.symm ho₁ ho₂ (by simp [hm₁, hm₂]) hpr
        exact absurd hd h.left 
  -/
  
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