import ReactorModel.Execution

open Classical ReactorType Indexable

-- TODO: Move this into `Objects.Reactor.Theorems`.
namespace ReactorType
namespace Wellformed

variable [Indexable α] {rtr : α} (wf : Wellformed rtr)

theorem shared_dep_local 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (hd₁ : ⟨cpt, j⟩ ∈ rcn₁.deps k)
    (hd₂ : ⟨cpt, j⟩ ∈ rcn₂.deps k) : rtr[.rcn][i₁]& = rtr[.rcn][i₂]& := by
  by_cases hi : i₁ = i₂
  case pos => simp_all
  case neg =>
    apply con?_eq_ext h₁ h₂
    intro _ _ hc₁ hc₂ hr₁ hr₂
    have hv₁ := wf.valid_deps hc₁ hr₁ hd₁
    have hv₂ := wf.valid_deps hc₂ hr₂ hd₂
    cases k <;> cases cpt <;> try cases ‹Kind› 
    case out.prt.in => exact absurd hd₂ $ wf.unique_inputs h₁ h₂ hi hd₁
    case in.prt.out =>
      cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> cases hk₁ ▸ hv₁ <;> cases hk₂ ▸ hv₂
      case _ hn₁ hj₁ _ _ hn₂ hj₂ =>
        have hc₁' := obj?_rtr_and_cpt?_to_obj? hc₁ (cpt := .rtr) hn₁
        have hc₂' := obj?_rtr_and_cpt?_to_obj? hc₂ (cpt := .rtr) hn₂
        have hj := mem_cpt?_rtr_eq hc₁' hc₂' (cpt := .prt .out) hj₁ hj₂
        have hn₁ := Partial.mem_iff.mpr ⟨_, hn₁⟩ 
        have hn₂ := Partial.mem_iff.mpr ⟨_, hn₂⟩ 
        injection hj with hj
        exact mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .rtr) hn₁ (hj ▸ hn₂)
    all_goals 
      cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> cases hk₁ ▸ hv₁ <;> cases hk₂ ▸ hv₂
      all_goals first 
        | exact mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .stv) ‹_› ‹_› 
        | exact mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .act) ‹_› ‹_›
        | exact mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .prt .out) ‹_› ‹_›
        | exact mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .prt .in) ‹_› ‹_›

theorem shared_state_local
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) 
    (hd₁ : ⟨.stv, j⟩ ∈ rcn₁.deps k₁) (hd₂ : ⟨.stv, j⟩ ∈ rcn₂.deps k₂) : 
    rtr[.rcn][i₁]& = rtr[.rcn][i₂]& := by
  apply con?_eq_ext h₁ h₂
  intro _ _ hc₁ hc₂ hr₁ hr₂
  have hv₁ := wf.valid_deps hc₁ hr₁ hd₁
  have hv₂ := wf.valid_deps hc₂ hr₂ hd₂
  cases hk₁ : rcn₁.kind <;> cases hk₂ : rcn₂.kind <;> cases hk₁ ▸ hv₁ <;> cases hk₂ ▸ hv₂
  all_goals exact mem_cpt?_rtr_eq hc₁ hc₂ (cpt := .stv) ‹_› ‹_› 

theorem hazards_prio' 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (hn : i₁ ≠ i₂)
    (hc : rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) (hd₁ : ⟨.stv, j⟩ ∈ rcn₁.deps k₁) 
    (hd₂ : ⟨.stv, j⟩ ∈ rcn₂.deps k₂) (hk : k₁ = .out ∨ k₂ = .out) :
    rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio :=
  have ⟨_, _, hc, hr₁, hr₂⟩ := obj?_con?_eq h₁ h₂ hc 
  wf.hazards_prio hc hr₁ hr₂ hn hd₁ hd₂ hk

theorem overlap_prio' 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (hn : i₁ ≠ i₂)
    (hc : rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) (hd₁ : d ∈ rcn₁.deps .out) (hd₂ : d ∈ rcn₂.deps .out) :
    rcn₁.prio < rcn₂.prio ∨ rcn₂.prio < rcn₁.prio :=
  have ⟨_, _, hc, hr₁, hr₂⟩ := obj?_con?_eq h₁ h₂ hc 
  wf.overlap_prio hc hr₁ hr₂ hn hd₁ hd₂

end Wellformed
end ReactorType

namespace Dependency

theorem prio' [Indexable α] {rtr : α}
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) 
    (hc : rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) (hm : rcn₁.Mutates ↔ rcn₂.Mutates) 
    (hp : rcn₁.prio > rcn₂.prio) : i₁ <[rtr] i₂ :=
  have ⟨_, _, hc, hr₁, hr₂⟩ := obj?_con?_eq h₁ h₂ hc 
  Dependency.prio hc hr₁ hr₂ hm hp

theorem mutNorm' [Indexable α] {rtr : α}
    (h₁ : rtr[.rcn][iₘ] = some m) (h₂ : rtr[.rcn][iₙ] = some n) (hm : m.Mutates) (hn : n.Normal)
    (hc : rtr[.rcn][iₘ]& = rtr[.rcn][iₙ]&) : iₘ <[rtr] iₙ :=
  have ⟨_, _, hc, hr₁, hr₂⟩ := obj?_con?_eq h₁ h₂ hc 
  Dependency.mutNorm hc hr₁ hr₂ hm hn

variable [Proper α] {rtr : α}

theorem same_con_shared_out_dep
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂)
    (hc : rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) (hn : i₁ ≠ i₂) (hd₁ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₁ .out) 
    (hd₂ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₂ .out) : (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) := by
  by_cases hm₁ : rcn₁.Mutates <;> by_cases hm₂ : rcn₂.Mutates
  rotate_left
  · exact .inl $ Dependency.mutNorm' h₁ h₂ hm₁ (by simp_all [Reaction.Mutates]) hc
  · exact .inr $ Dependency.mutNorm' h₂ h₁ hm₂ (by simp_all [Reaction.Mutates]) hc.symm
  all_goals
    cases Proper.wellformed rtr |>.overlap_prio' h₁ h₂ hn hc hd₁ hd₂
    · exact .inr $ Dependency.prio' h₂ h₁ hc.symm (by simp_all) ‹_›
    · exact .inl $ Dependency.prio' h₁ h₂ hc (by simp_all) ‹_›

theorem shared_out_dep
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (hn : i₁ ≠ i₂)
    (hd₁ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₁ .out) (hd₂ : ⟨cpt, i⟩ ∈ Reaction.deps rcn₂ .out) :
    (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) := by  
  have hc := Proper.wellformed rtr |>.shared_dep_local h₁ h₂ hd₁ hd₂
  exact same_con_shared_out_dep h₁ h₂ hc hn hd₁ hd₂

theorem hazard 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (hn : i₁ ≠ i₂)
    (hc : rtr[.rcn][i₁]& = rtr[.rcn][i₂]&) (hd₁ : ⟨.stv, i⟩ ∈ Reaction.deps rcn₁ k₁) 
    (hd₂ : ⟨.stv, i⟩ ∈ Reaction.deps rcn₂ k₂) (hk : k₁ = .out ∨ k₂ = .out) : 
    (i₁ <[rtr] i₂) ∨ (i₂ <[rtr] i₁) := by  
  by_cases hm₁ : rcn₁.Mutates <;> by_cases hm₂ : rcn₂.Mutates
  rotate_left
  · exact .inl $ Dependency.mutNorm' ‹_› ‹_› hm₁ (by simp_all [Reaction.Mutates]) hc
  · exact .inr $ Dependency.mutNorm' ‹_› ‹_› hm₂ (by simp_all [Reaction.Mutates]) hc.symm
  all_goals
    cases Proper.wellformed rtr |>.hazards_prio' h₁ h₂ hn hc hd₁ hd₂ hk
    · exact .inr $ Dependency.prio' h₂ h₁ hc.symm (by simp_all) ‹_›
    · exact .inl $ Dependency.prio' h₁ h₂ hc (by simp_all) ‹_›

end Dependency

-- This proposition states that `rcn₂` does not depend on `rcn₁`.
abbrev NotDependent [Indexable α] (rtr : α) (rcn₁ rcn₂ : ID) : Prop :=
  ¬(rcn₁ <[rtr] rcn₂)

notation:50 rcn₁ " ≮[" rtr "] " rcn₂ => NotDependent rtr rcn₁ rcn₂

theorem NotDependent.equiv [Indexable α] {rtr₁ rtr₂ : α} (h : i₁ ≮[rtr₁] i₂) (e : rtr₁ ≈ rtr₂) : 
    i₁ ≮[rtr₂] i₂ :=
  fun d => absurd (d.equiv e) h

theorem NotDependent.deps_disjoint [Indexable α] {rtr : α} {d} (hi : i₁ ≮[rtr] i₂) 
    (h₁ : rtr[.rcn][i₁] = some rcn₁) (h₂ : rtr[.rcn][i₂] = some rcn₂) (h : d ∈ rcn₁.deps .out) 
    (hs : d.cpt ≠ .stv) : d ∉ rcn₂.deps .in :=
  byContradiction fun hd => absurd (Dependency.depOverlap h₁ h₂ h (not_not.mp hd) hs) hi

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
  have hc := Proper.wellformed rtr |>.shared_state_local h₁ h₂ hd₁ hd₂
  cases Dependency.hazard h₁ h₂ hi.not_eq hc hd₁ hd₂ (.inl rfl) <;> simp [hi.left, hi.right] at *

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