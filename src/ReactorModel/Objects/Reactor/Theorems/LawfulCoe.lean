import ReactorModel.Objects.Reactor.Theorems.Indexable
import ReactorModel.Objects.Reactor.Proper





theorem UniqueIDs.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} 
    (h : UniqueIDs (rtr : β)) : UniqueIDs rtr where
  allEq m₁ m₂ :=
    h.allEq (.fromLawfulCoe m₁) (.fromLawfulCoe m₂) ▸ Member.Equivalent.from_lawfulCoe m₁ 
      |>.trans (Member.Equivalent.from_lawfulCoe m₂).symm 
      |>.to_eq

instance [LawfulUpdatable α] [ind : Indexable β] [LawfulCoe α β] : Indexable α where
  unique_ids := UniqueIDs.lift ind.unique_ids 






class LawfulCoe (α β) [ReactorType α] [ReactorType β] extends Coe α β where
  inj          : coe.Injective := by lawfulCoe_inj_proof
  get?_val_coe : get? (coe rtr) (cpt : Component.Valued) = get? rtr cpt
  get?_rcn_coe : get? (coe rtr) .rcn = get? rtr .rcn
  get?_rtr_coe : get? (coe rtr) .rtr = (get? rtr .rtr).map coe := by lawfulCoe_nest_proof








noncomputable section
open Classical Reactor

namespace ReactorType

scoped macro "lawfulCoe_nest_proof" : tactic => 
  `(tactic| simp [ReactorType.nest, Partial.map_map, Function.comp, Partial.attach_map_val])

scoped macro "lawfulCoe_inj_proof" : tactic => 
  `(tactic| (simp [Function.Injective]; intro ⟨_, _⟩ ⟨_, _⟩; simp))

class LawfulCoe (α β) [a : ReactorType α] [b : ReactorType β] extends Coe α β where
  ports : b.ports ∘ coe = a.ports                    := by rfl
  acts  : b.acts  ∘ coe = a.acts                     := by rfl
  rcns  : b.rcns  ∘ coe = a.rcns                     := by rfl
  state : b.state ∘ coe = a.state                    := by rfl
  nest  : b.nest  ∘ coe = (Partial.map coe) ∘ a.nest := by lawfulCoe_nest_proof
  inj   : coe.Injective                              := by lawfulCoe_inj_proof

namespace LawfulCoe

variable [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] {rtr : α}

theorem nest' [a : ReactorType α] [b : ReactorType β] [c : LawfulCoe α β] :
    b.nest (c.coe rtr) = (a.nest rtr).map c.coe := by
  rw [←Function.comp_apply (f := ReactorType.nest), c.nest]
  simp

theorem coe_ext_iff [ReactorType α] [ReactorType β] [c : LawfulCoe α β] 
    {rtr₁ rtr₂ : α} : rtr₁ = rtr₂ ↔ (rtr₁ : β) = (rtr₂ : β) :=
  ⟨(congr_arg _ ·), (c.inj ·)⟩

instance : Coe (a.cptType cpt) (b.cptType cpt) where
  coe := 
    match cpt with
    | .rcn | .prt _ | .act | .stv => id
    | .rtr => c.coe

theorem lower_cpt?_eq_some (cpt) {o} (h : a.cpt? cpt rtr i = some o) : 
    b.cpt? cpt rtr i = some ↑o := by
  split <;> simp_all [cpt?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val]
  exists o

theorem lower_mem_cpt? (cpt) (h : i ∈ a.cpt? cpt rtr) : i ∈ b.cpt? cpt rtr :=
  ⟨h.choose, c.lower_cpt?_eq_some _ h.choose_spec⟩ 

theorem lift_cpt?_eq_none (cpt) {i : ID} 
    (h : b.cpt? cpt rtr i = none) : a.cpt? cpt rtr i = none := by
  cases cpt <;> try cases ‹Component.Valued›
  all_goals simp_all [cpt?, ←c.rcns, ←c.ports, ←c.acts, ←c.state] 
  simp [c.nest', Partial.map_val] at h
  exact h

theorem lift_cpt?_eq_some (cpt) {i : ID} {o : a.cptType cpt} (h : b.cpt? cpt rtr i = some ↑o) : 
    a.cpt? cpt rtr i = some o := by
  split at h <;> simp_all [cpt?, ←c.rcns, ←c.ports, ←c.acts, ←c.state]
  simp [c.nest', Partial.map_val] at h
  have ⟨_, _, h⟩ := h
  cases c.inj h
  assumption

theorem lift_nest_eq_some {i : ID} (h : b.nest rtr i = some n₂) : 
    ∃ n₁, (a.nest rtr i = some n₁) ∧ ((n₁ : β) = n₂) := by
  simp [c.nest', Partial.map_val] at h
  exact h

-- Note: This theorem excludes `cpt = .rtr`, because that case is harder than the other cases and we
--       only ever use this theorem for `cpt = .act` anyway.
theorem lift_mem_cpt? (cpt) (h : i ∈ b.cpt? cpt rtr) (hc : cpt ≠ .rtr := by simp) : 
    i ∈ a.cpt? cpt rtr := by
  cases cpt <;> try cases ‹Component.Valued›  
  case rtr => contradiction
  all_goals exact ⟨h.choose, c.lift_cpt?_eq_some _ h.choose_spec⟩ 

end LawfulCoe

def Member.fromLawfulCoe [ReactorType α] [ReactorType β] [c : LawfulCoe α β] {rtr : α} : 
    (Member cpt i rtr) → Member cpt i (rtr : β)
  | final h  => final (c.lower_mem_cpt? _ h)
  | nest h m => nest (c.lower_cpt?_eq_some (cpt := .rtr) h) (fromLawfulCoe m)

instance [ReactorType α] [ReactorType β] [c : LawfulCoe α β] {rtr : α} :
    Coe (Member cpt i rtr) (Member cpt i (rtr : β)) where
  coe := Member.fromLawfulCoe

instance [ReactorType α] [e : Extensional β] [c : LawfulCoe α β] : Extensional α where
  ext_iff := by
    intro rtr₁ rtr₂ 
    simp [c.coe_ext_iff, e.ext_iff, ←c.ports, ←c.acts, ←c.rcns, ←c.state, c.nest']
    intros
    exact {
      mp := Partial.map_inj (by simp [Function.Injective, c.coe_ext_iff])
      mpr := by simp_all
    }

instance [Extensional α] [b : ReactorType.WellFounded β] [c : LawfulCoe α β] : 
    ReactorType.WellFounded α where
  wf := by
    suffices h : InvImage Nested c.coe = Nested from h ▸ InvImage.wf c.coe b.wf
    funext rtr₁ rtr₂
    simp [Nested, InvImage, c.nest', Partial.map_val]
    exact ⟨fun ⟨_, ⟨_, hn, h⟩⟩ => ⟨_, c.inj h ▸ hn⟩, fun ⟨i, h⟩ => ⟨i, rtr₁, by simp [h]⟩⟩  

variable [ReactorType α] [ReactorType β] in section

theorem RootEqualUpTo.lift [l : LawfulCoe α β] {rtr₁ rtr₂ : α} 
    (e : RootEqualUpTo cpt i (rtr₁ : β) (rtr₂ : β)) : RootEqualUpTo cpt i rtr₁ rtr₂ := by
  intro c j h
  have he := e h
  cases h₁ : cpt? c (rtr₁ : β) j <;> cases h₂ : cpt? c (rtr₂ : β) j <;> simp_all
  case none.none => simp [l.lift_cpt?_eq_none _ h₁, l.lift_cpt?_eq_none _ h₂]
  case some.some => 
    cases c <;> try cases ‹Reactor.Component.Valued› 
    all_goals try simp [l.lift_cpt?_eq_some _ h₁, l.lift_cpt?_eq_some _ h₂]
    case rtr =>
      have ⟨_, _, h₁'⟩ := l.lift_nest_eq_some h₁
      have ⟨_, _, h₂'⟩ := l.lift_nest_eq_some h₂
      subst h₁'
      simp [l.lift_cpt?_eq_some _ h₁, l.lift_cpt?_eq_some _ h₂]

def LawfulMemUpdate.lift [c : LawfulCoe α β] {rtr₁ rtr₂ : α} :
    (LawfulMemUpdate cpt i f (rtr₁ : β) (rtr₂ : β)) → LawfulMemUpdate cpt i f rtr₁ rtr₂
  | final e h₁ h₂ (o := o) => 
    have h₁ : cpt? cpt rtr₁ i = some o     := by cases cpt <;> exact c.lift_cpt?_eq_some _ h₁
    have h₂ : cpt? cpt rtr₂ i = some (f o) := by cases cpt <;> exact c.lift_cpt?_eq_some _ h₂
    .final e.lift h₁ h₂
  | nest (n₁ := n₁) (n₂ := n₂) e h₁ h₂ u (j := j) => 
    have o₁ := c.lift_nest_eq_some h₁
    have o₂ := c.lift_nest_eq_some h₂
    have ⟨h₁, h₁'⟩ := o₁.choose_spec
    have ⟨h₂, h₂'⟩ := o₂.choose_spec 
    let u' : LawfulMemUpdate cpt i f (o₁.choose : β) (o₂.choose : β) := cast (by simp [h₁', h₂']) u
    .nest e.lift h₁ h₂ u'.lift
termination_by lift u => sizeOf u
decreasing_by simp_wf; have h : sizeOf u' = sizeOf u := (by congr; apply cast_heq); simp [h]

-- TODO:
-- If we consider the following following diagram:
-- 
--     rtr₁ -u.lift→ rtr₂
--      |             |
--     coe           coe
--      ↓             ↓
-- (rtr₁ : β) -u→ (rtr₂ : β)
--
-- ... there's something functorial about this. The `lift` looks like a functor's `map` over `u`.
-- Figure out if there's a way of modelling some part of this as a functor. 
def LawfulUpdate.lift [c : LawfulCoe α β] {rtr₁ rtr₂ : α} :
    (LawfulUpdate cpt i f (rtr₁ : β) (rtr₂ : β)) → LawfulUpdate cpt i f rtr₁ rtr₂
  | update u => update u.lift
  | notMem h eq =>  
    let u := notMem (byContradiction (h.false $ not_isEmpty_iff.mp · |>.some.fromLawfulCoe)) rfl
    (c.inj eq) ▸ u 

end

scoped macro "lawfulUpdatableCoe_update_coe_comm_proof" : tactic =>
  `(tactic| simp [Updatable.update, Coe.coe])

class LawfulUpdatableCoe (α β) [a : Updatable α] [b : Updatable β] extends LawfulCoe α β where
  update_coe_comm : 
    ∀ {rtr cpt i f}, b.update (coe rtr) cpt i f = coe (a.update rtr cpt i f) := by 
      lawfulUpdatableCoe_update_coe_comm_proof

instance [Updatable α] [LawfulUpdatable β] [c : LawfulUpdatableCoe α β] : LawfulUpdatable α where
  lawful rtr cpt i f := c.update_coe_comm ▸ LawfulUpdatable.lawful (rtr : β) cpt i f |>.lift 

variable [a : Indexable α] [b : Indexable β] [c : LawfulCoe α β] {rtr : α}

namespace LawfulCoe

theorem lower_container_eq {m : Member cpt i rtr} (h : m.container = con) : 
    (m : Member cpt i (rtr : β)).container = ↑con := by
  induction m
  case final =>
    simp [Member.container] at h ⊢
    simp [←h]
  case nest m hi => 
    cases m 
    case final => 
      simp [Member.fromLawfulCoe, Member.container] at h ⊢
      simp [← h] 
    case nest hi =>
      simp [Member.container] at h
      simp [←hi h, Member.fromLawfulCoe, Member.container]

theorem lower_con?_some (h : rtr[cpt][i]& = some con) : (rtr : β)[cpt][i]& = some ↑con := by
  simp [Indexable.con?] at h ⊢
  split at h
  case inr => contradiction 
  case inl n =>
    injection h with h
    simp [(⟨n.some⟩ : Nonempty (Member cpt i (rtr : β)))]
    simp [←c.lower_container_eq h, (⟨n.some⟩ : Nonempty (Member cpt i (rtr : β)))]
    congr
    apply b.unique_ids.allEq

theorem lower_obj?_some {i o} (h : rtr[cpt][i] = some o) : (rtr : β)[cpt][i] = some ↑o := by
  cases cpt <;> try cases i
  case rtr.none => simp_all [Indexable.obj?]
  all_goals
    have ⟨_, h₁, h₂⟩ := a.obj?_to_con?_and_cpt? h
    simp [Indexable.obj?, bind, c.lower_con?_some h₁, c.lower_cpt?_eq_some _ h₂]

theorem lower_mem_obj? {i} (h : i ∈ rtr[cpt]) : i ∈ (rtr : β)[cpt] :=
  Partial.mem_iff.mpr ⟨_, c.lower_obj?_some (Partial.mem_iff.mp h).choose_spec⟩ 

end LawfulCoe

theorem Dependency.lower [c : LawfulCoe α β] (d : i₁ <[rtr] i₂) : i₁ <[(rtr : β)] i₂ := by
  induction d with
  | prio h₁ h₂ h₃ =>
    exact prio (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rcn h₂) (c.lower_cpt?_eq_some .rcn h₃) 
           ‹_› ‹_›
  | mutNorm h₁ h₂ h₃ => 
    exact mutNorm (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rcn h₂)
          (c.lower_cpt?_eq_some .rcn h₃) ‹_› ‹_›
  | depOverlap h₁ h₂ => 
    exact depOverlap (c.lower_obj?_some h₁) (c.lower_obj?_some h₂) ‹_› ‹_› ‹_›
  | mutNest h₁ h₂ h₃ _ h₄ => 
    exact mutNest (c.lower_obj?_some h₁) (c.lower_cpt?_eq_some .rtr h₂)
          (c.lower_cpt?_eq_some .rcn h₃) ‹_› (c.lower_mem_cpt? .rcn h₄) 
  | trans _ _ d₁ d₂ => 
    exact trans d₁ d₂

theorem Dependency.Acyclic.lift [LawfulCoe α β] (a : Acyclic (rtr : β)) : Acyclic rtr :=
  (a · $ ·.lower)
  
namespace Wellformed

set_option hygiene false in
scoped macro "lift_nested_proof " name:ident : term => `(
  fun hc hp => by
    have h := LawfulCoe.nest' (rtr := rtr) (β := β) ▸ hc 
    simp [Partial.map_val] at h
    obtain ⟨_, _, h⟩ := h
    subst h
    exact $(Lean.mkIdentFrom name $ `ValidDependency ++ name.getId) 
      (LawfulCoe.lift_cpt?_eq_some .rtr hc) (LawfulCoe.lift_mem_cpt? (.prt _) hp)
)

theorem ValidDependency.lift [ReactorType α] [ReactorType β] [LawfulCoe α β] {rtr : α} : 
    (ValidDependency (rtr : β) rk dk d) → ValidDependency rtr rk dk d 
  | stv h           => stv $ LawfulCoe.lift_mem_cpt? .stv h
  | act h           => act $ LawfulCoe.lift_mem_cpt? .act h
  | prt h           => prt $ LawfulCoe.lift_mem_cpt? (.prt _) h
  | nestedIn hc hp  => (lift_nested_proof nestedIn) hc hp
  | nestedOut hc hp => (lift_nested_proof nestedOut) hc hp
    
set_option hygiene false in 
scoped macro "lift_prio_proof " name:ident : term => `(
  fun h₁ h₂ h₃ => 
    $(Lean.mkIdentFrom name $ `Wellformed ++ name.getId) ‹Wellformed (_ : β)› 
      (LawfulCoe.lower_obj?_some h₁) (LawfulCoe.lower_cpt?_eq_some .rcn h₂) 
      (LawfulCoe.lower_cpt?_eq_some .rcn h₃)
)

open LawfulCoe in
theorem lift [Indexable α] [Indexable β] [LawfulCoe α β] {rtr : α} (wf : Wellformed (rtr : β)) : 
    Wellformed rtr where
  overlap_prio        := lift_prio_proof overlap_prio
  hazards_prio        := lift_prio_proof hazards_prio
  mutation_prio       := lift_prio_proof mutation_prio
  acyclic_deps        := wf.acyclic_deps.lift
  valid_deps h₁ h₂ h₃ := wf.valid_deps (lower_obj?_some h₁) (lower_cpt?_eq_some .rcn h₂) h₃ |>.lift
  unique_inputs h₁ h₂ := wf.unique_inputs (lower_obj?_some h₁) (lower_obj?_some h₂)

end Wellformed
end ReactorType