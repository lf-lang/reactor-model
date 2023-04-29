import ReactorModel.Objects.Reactor.Updatable
import ReactorModel.Objects.Reactor.Indexable

noncomputable section
open Classical

namespace ReactorType

/- ---------------------------------------------------------------------------------------------- -/
namespace RootEqualUpTo

variable [ReactorType α] {rtr₁ : α}

@[refl]
theorem refl (rtr₁ : α) : rtr₁ ≃[cpt][i] rtr₁ :=
  fun _ => rfl

@[symm]
theorem symm (e : rtr₁ ≃[cpt][i] rtr₂) : rtr₂ ≃[cpt][i] rtr₁ :=
  (e · |>.symm)

@[trans]
theorem trans (e₁ : rtr₁ ≃[cpt][i] rtr₂) (e₂ : rtr₂ ≃[cpt][i] rtr₃) : rtr₁ ≃[cpt][i] rtr₃ :=
  fun h => (e₁ h).trans (e₂ h)

instance : Equivalence ((· : α) ≃[cpt][i] ·) :=
  { refl, symm, trans }

theorem mem_iff (e : rtr₁ ≃[cpt][i] rtr₂) (h : c ≠ cpt ∨ j ≠ i) : j ∈ rtr₁{c} ↔ j ∈ rtr₂{c} := by
  simp [Partial.mem_iff]
  exact ⟨(e h ▸ ·), (e h ▸ ·)⟩   

theorem valued {c cpt : Component.Valued} (e : rtr₁ ≃[cpt][i] rtr₂) (h : c ≠ cpt ∨ j ≠ i) : 
    rtr₁{c}{j} = rtr₂{c}{j} := 
  e $ h.elim (by simp [*]) Or.inr  

end RootEqualUpTo

/- ---------------------------------------------------------------------------------------------- -/

inductive Equivalent [inst : ReactorType α] : α → α → Prop
  | refl (rtr) : Equivalent rtr rtr
  | struct
    (mem_get?_iff : ∀ cpt i, i ∈ rtr₁{cpt} ↔ i ∈ rtr₂{cpt}) 
    (get?_rcn_some_eq : ∀ {i r₁ r₂}, (rtr₁{.rcn}{i} = some r₁) → (rtr₂{.rcn}{i} = some r₂) → r₁ = r₂) 
    (get?_rtr_some_equiv : ∀ {i n₁ n₂}, (rtr₁{.rtr}{i} = some n₁) → (rtr₂{.rtr}{i} = some n₂) → Equivalent (inst := inst) n₁ n₂) 
    : Equivalent rtr₁ rtr₂
 
namespace Equivalent

variable [ReactorType α] {rtr₁ : α}

instance : HasEquiv α where 
  Equiv := Equivalent

@[symm]
theorem symm (e : rtr₁ ≈ rtr₂) : rtr₂ ≈ rtr₁ := by
  induction e
  case refl => exact .refl _
  case struct h₁ h₂ _ hi => 
    constructor <;> intros
    · exact h₁ ‹_› ‹_› |>.symm
    · exact h₂ ‹_› ‹_› |>.symm
    · exact hi ‹_› ‹_›

@[trans]
theorem trans (e₁ : rtr₁ ≈ rtr₂) (e₂ : rtr₂ ≈ rtr₃) : rtr₁ ≈ rtr₃ := by
  induction e₁ generalizing rtr₃
  case refl => exact e₂
  case struct h₁ h₂ _ hi =>
    cases e₂
    case refl => exact .struct ‹_› ‹_› ‹_› 
    case struct h₁' h₂' h₃'=> 
      apply Equivalent.struct
      · intros; exact h₁ ‹_› ‹_› |>.trans (h₁' ‹_› ‹_›)
      · intro _ _ _ h _
        have ⟨_, h⟩ := Partial.mem_iff.mp <| h₁ .rcn ‹_› |>.mp $ Partial.mem_iff.mpr ⟨_, h⟩
        exact h₂ ‹_› h |>.trans (h₂' h ‹_›)
      · intro _ _ _ h _
        have ⟨_, h⟩ := Partial.mem_iff.mp <| h₁ .rtr ‹_› |>.mp $ Partial.mem_iff.mpr ⟨_, h⟩ 
        exact hi ‹_› h (h₃' h ‹_›)

instance : Equivalence ((· : α) ≈ ·) := 
  { refl, symm, trans }

theorem mem_get?_iff : (rtr₁ ≈ rtr₂) → (i ∈ rtr₁{cpt} ↔ i ∈ rtr₂{cpt})
  | refl _      => Iff.refl _
  | struct h .. => h _ _

theorem get?_rcn_some_eq : 
    (rtr₁ ≈ rtr₂) → (rtr₁{.rcn}{i} = some r₁) → (rtr₂{.rcn}{i} = some r₂) → r₁ = r₂
  | refl _       => by simp_all
  | struct _ h _ => h

theorem get?_rtr_some_equiv : 
    (rtr₁ ≈ rtr₂) → (rtr₁{.rtr}{i} = some n₁) → (rtr₂{.rtr}{i} = some n₂) → n₁ ≈ n₂
  | refl _       => by intros; simp_all; exact .refl _
  | struct _ _ h => h

theorem get?_some_iff (e : rtr₁ ≈ rtr₂) : 
    (∃ o, rtr₁{cpt}{i} = some o) ↔ (∃ o, rtr₂{cpt}{i} = some o) := by
  simp [←Partial.mem_iff, mem_get?_iff e]

theorem get?_none_iff (e : rtr₁ ≈ rtr₂) : (rtr₁{cpt}{i} = none) ↔ (rtr₂{cpt}{i} = none) := by
  simp only [Option.eq_none_iff_forall_not_mem, ←not_exists]
  simp [get?_some_iff e]

theorem get?_rcn_eq (e : rtr₁ ≈ rtr₂) : rtr₂{.rcn} = rtr₁{.rcn} := by
  funext i
  by_cases h₁ : ∃ o, rtr₁{.rcn}{i} = some o
  case pos =>
    have ⟨_, h₂⟩ := get?_some_iff e |>.mp h₁
    have ⟨_, h₁⟩ := h₁
    exact get?_rcn_some_eq e h₁ h₂ ▸ h₁ |>.symm ▸ h₂
  case neg =>
    have h₂ := get?_some_iff e |>.not.mp h₁
    push_neg at h₁ h₂
    simp [Option.eq_none_iff_forall_not_mem.mpr h₁, Option.eq_none_iff_forall_not_mem.mpr h₂]

end Equivalent

/- ---------------------------------------------------------------------------------------------- -/
namespace LawfulMemUpdate

variable [ReactorType α]

def member₁ {rtr₁ : α} : (LawfulMemUpdate cpt i v rtr₁ rtr₂) → StrictMember cpt i rtr₁
  | final _ h _  => .final h
  | nested _ h _ u => .nested h u.member₁

def member₂ {rtr₁ : α} : (LawfulMemUpdate cpt i v rtr₁ rtr₂) → StrictMember cpt i rtr₂
  | final _ _ h  => .final h
  | nested _ _ h u => .nested h u.member₂
  
theorem equiv {rtr₁ : α} (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) : rtr₁ ≈ rtr₂ := by
  induction u <;> constructor
  case final.mem_get?_iff e h₁ h₂ =>
    intro c j
    by_cases hc : c = cpt <;> try subst hc
    case neg => exact e.mem_iff (.inl hc)
    case pos =>
      by_cases hj : j = i <;> try subst hj
      case neg => exact e.mem_iff (.inr hj)
      case pos => simp [Partial.mem_iff, h₁, h₂]
  case final.get?_rcn_some_eq e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all
  case final.get?_rtr_some_equiv e _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rtr) (j := j) (.inl $ by simp)
    simp_all
    apply Equivalent.refl
  case nested.mem_get?_iff j _ _ _ _ e h₁ h₂ _ _ =>
    intro c j'
    by_cases hc : c = .rtr <;> try subst hc
    case neg => exact e.mem_iff (.inl hc)
    case pos => 
      by_cases hj : j' = j <;> try subst hj
      case neg => exact e.mem_iff (.inr hj)
      case pos => simp [Partial.mem_iff, h₁, h₂]
  case nested.get?_rcn_some_eq e h₁ h₂ _ _ =>
    intro j _ _ h₁ h₂
    have h := e (c := .rcn) (j := j) (.inl $ by simp)
    simp_all
  case nested.get?_rtr_some_equiv j _ _ _ _ e _ _ _ hi =>
    intro j' n₁' n₂' h₁' h₂'
    by_cases hj : j' = j <;> try subst hj
    case pos => simp_all; assumption
    case neg => 
      have := e (c := .rtr) (j := j') (.inr hj)
      simp_all
      apply Equivalent.refl

end LawfulMemUpdate

theorem LawfulUpdate.equiv [ReactorType α] {rtr₁ : α} :
    (LawfulUpdate cpt i v rtr₁ rtr₂) → rtr₁ ≈ rtr₂
  | notMem _ h => h ▸ (.refl _)
  | update u   => u.equiv

theorem LawfulUpdatable.equiv [LawfulUpdatable α] {rtr : α} : 
    rtr ≈ (Updatable.update rtr cpt i f) := 
  (lawful rtr cpt i f).equiv

/- ---------------------------------------------------------------------------------------------- -/
namespace StrictMember

variable [ReactorType α] {rtr : α} in section

theorem nested_object (s : StrictMember cpt i' rtr') (h : rtr{.rtr}{i} = some rtr') :
    (nested h s).object = s.object := 
  rfl

def split : 
    {rtr rtr' : α} → (s : StrictMember cpt i' rtr') → (rtr{.rtr}{i} = some rtr') → 
    (j : ID) × { s' : StrictMember .rtr j rtr // s'.object{cpt}{i'} = s.object }
  | _, _, final hn, h => ⟨i, ⟨final h, hn⟩⟩
  | _, _, nested hn s, h => let ⟨j, ⟨s', hs'⟩⟩ := split s hn; ⟨j, ⟨nested h s', hs'⟩⟩

def split' : 
    (s : StrictMember cpt i rtr) → 
    (j : WithTop ID) × { m : Member .rtr j rtr // m.object{cpt}{i} = s.object } 
  | final h     => ⟨⊤, ⟨.root, h⟩⟩
  | nested hn s => let ⟨j, ⟨s', hs'⟩⟩ := split s hn; ⟨j, ⟨.strict s', hs'⟩⟩

def extend : 
    {rtr : α} → (s : StrictMember .rtr i rtr) → (s.object{cpt}{j} = some o) → StrictMember cpt j rtr
  | _, final hn,    h => nested hn (final h)
  | _, nested hn s, h => nested hn (extend s h)

theorem extend_object :
    {rtr : α} → (s : StrictMember .rtr i rtr) → (h : s.object{cpt}{j} = some o) → 
    (s.extend h).object = o
  | _, final _,    _ => rfl
  | _, nested _ s, h => extend_object s h

theorem extend_not_final (s : StrictMember .rtr i rtr) (h : s.object{cpt}{j} = some o)
    (hf : rtr{cpt}{j} = some o') : s.extend h ≠ final hf := by
  cases s <;> simp [extend]

theorem extend_inj 
    {s₁ : StrictMember .rtr i₁ rtr} {s₂ : StrictMember .rtr i₂ rtr}
    {h₁ : s₁.object{cpt}{j} = some o₁} {h₂ : s₂.object{cpt}{j} = some o₂}
    (h : s₁.extend h₁ = s₂.extend h₂) : i₁ = i₂ := by
  induction s₁ generalizing i₂ <;> cases s₂
  all_goals simp [extend] at h; obtain ⟨hj, hr, h⟩ := h; subst hj hr 
  case final.final  => rfl
  case nested.nested hi _ _ => exact hi $ eq_of_heq h
  case final.nested => exact absurd (eq_of_heq h).symm $ StrictMember.extend_not_final _ _ _
  case nested.final => exact absurd (eq_of_heq h) $ StrictMember.extend_not_final _ _ _

theorem extend_split (s : StrictMember cpt i' rtr') (h : rtr{.rtr}{i} = some rtr') :
    extend (split s h).snd.val (split s h).snd.property = nested h s := by
  induction s generalizing rtr i <;> simp [extend]
  case nested h' _ hi => exact hi h'

def fromLawfulMemUpdate {rtr₁ : α} : 
    (StrictMember c j rtr₂) → (LawfulMemUpdate cpt i v rtr₁ rtr₂) → StrictMember c j rtr₁
  | final h, u               => final $ (Equivalent.get?_some_iff u.equiv).mpr ⟨_, h⟩ |>.choose_spec
  | nested h s, .final e _ _ => nested (h ▸ e (.inl $ by simp)) s 
  | nested h s (j := j₂), .nested e h₁ h₂ u (j := j₁) =>
      if hj : j₂ = j₁ 
      then nested h₁ $ fromLawfulMemUpdate ((Option.some_inj.mp $ h₂ ▸ hj ▸ h) ▸ s) u
      else nested (h ▸ e $ .inr hj) s 

def fromLawfulUpdate {rtr₂ : α} (s : StrictMember c j rtr₂) : 
    (LawfulUpdate cpt i v rtr₁ rtr₂) → StrictMember c j rtr₁
  | .notMem _ h => h ▸ s
  | .update u   => s.fromLawfulMemUpdate u

def fromEquiv {rtr₁ : α} (e : rtr₁ ≈ rtr₂) : 
    (StrictMember cpt i rtr₁) → StrictMember cpt i rtr₂
  | final h    => final (e.get?_some_iff.mp ⟨_, h⟩).choose_spec
  | nested h m => 
    have h' := (Equivalent.get?_some_iff e).mp ⟨_, h⟩ 
    have e' := Equivalent.get?_rtr_some_equiv e h h'.choose_spec
    nested h'.choose_spec (fromEquiv e' m)

end

inductive Equivalent : 
    {α : Type} → {β : Type} → [ReactorType α] → [ReactorType β] → {rtr₁ : α} → {rtr₂ : β} → 
    (StrictMember cpt i rtr₁) → (StrictMember cpt i rtr₂) → Prop 
  | refl [ReactorType α] {rtr : α} (s : StrictMember cpt i rtr) : Equivalent s s
  | final [ReactorType α] [ReactorType β] {rtr₁ : α} {rtr₂ : β} 
    (h₁ : rtr₁{cpt}{i} = some o₁) (h₂ : rtr₂{cpt}{i} = some o₂) : Equivalent (final h₁) (final h₂)
  | nested [ReactorType α] [ReactorType β] {rtr₁ : α} {rtr₂ : β} {n₁ : α} {n₂ : β} 
    {s₁ : StrictMember cpt i n₁} {s₂ : StrictMember cpt i n₂} (h₁ : rtr₁{.rtr}{j} = some n₁) 
    (h₂ : rtr₂{.rtr}{j} = some n₂) : (Equivalent s₁ s₂) → Equivalent (nested h₁ s₁) (nested h₂ s₂)

namespace Equivalent

variable [ReactorType α] {rtr₁ : α}

instance [ReactorType β] {rtr₂ : β} : 
    HasHEquiv (StrictMember cpt i rtr₁) (StrictMember cpt i rtr₂) where
  HEquiv := Equivalent (cpt := cpt) (i := i) (rtr₁ := rtr₁) (rtr₂ := rtr₂)

theorem symm [ReactorType β] {rtr₂ : β} 
    {s₁ : StrictMember cpt i rtr₁} {s₂ : StrictMember cpt i rtr₂} (e : s₁ ∼ s₂) : s₂ ∼ s₁ := by
  induction e <;> constructor; assumption

theorem trans [ReactorType β] [ReactorType γ] {rtr₂ : β} {rtr₃ : γ}
    {s₁ : StrictMember cpt i rtr₁} {s₂ : StrictMember cpt i rtr₂} {s₃ : StrictMember cpt i rtr₃}
    (e₁ : s₁ ∼ s₂) (e₂ : s₂ ∼ s₃) : s₁ ∼ s₃ := by
  induction e₁ generalizing rtr₃ <;> cases e₂ <;> constructor <;> try assumption
  case nested.nested hi₁ _ _ _ _ hi₂ => exact hi₁ hi₂

instance {rtr : α} : Equivalence (Equivalent (· : StrictMember cpt i rtr) ·) := 
  { refl, symm, trans }

theorem to_eq {rtr : α} {s₁ s₂ : StrictMember cpt i rtr} : (s₁ ∼ s₂) → s₁ = s₂
  | refl _         => rfl
  | final h₁ h₂    => by simp [Option.some_inj.mp $ h₁ ▸ h₂]
  | nested h₁ h₂ e => by cases Option.some_inj.mp $ h₁ ▸ h₂; simp [to_eq e]

theorem fromLawfulMemUpdate (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) (s : StrictMember c j rtr₂) : 
    s ∼ s.fromLawfulMemUpdate u := by
  induction u <;> cases s <;> (simp [StrictMember.fromLawfulMemUpdate]; try exact final _ _)
  case final.nested e _ _ _ _ _ hn => exact nested hn (e (c := .rtr) (.inl $ by simp) ▸ hn) (refl _)
  case nested.nested e h₁ h₂ _ hi _ _ m hn =>
    split
    case inl hj => cases hj; cases Option.some_inj.mp $ h₂ ▸ hn; exact nested hn h₁ (hi m)
    case inr hj => exact nested hn (hn ▸ e (.inr hj)) (refl _)

theorem fromLawfulUpdate (u : LawfulUpdate cpt i v rtr₁ rtr₂) (s : StrictMember c j rtr₂) : 
    s ∼ s.fromLawfulUpdate u := by
  cases u
  case notMem   => cases ‹_ = _›; apply refl
  case update u => exact fromLawfulMemUpdate u s 

end Equivalent
end StrictMember

/- ---------------------------------------------------------------------------------------------- -/
namespace Member

variable [ReactorType α] {rtr rtr₁ : α}

def extend : (m : Member .rtr i rtr) → (m.object{cpt}{j} = some o) → Member cpt j rtr
  | root,     h => final h
  | strict s, h => s.extend h

theorem extend_object : 
    (m : Member .rtr i rtr) → (h : m.object{cpt}{j} = some o) → (m.extend h).object = o
  | root,     h => rfl
  | strict s, h => s.extend_object h

theorem extend_inj
    {m₁ : Member .rtr i₁ rtr} {m₂ : Member .rtr i₂ rtr} {h₁ : m₁.object{cpt}{j} = some o₁} 
    {h₂ : m₂.object{cpt}{j} = some o₂} (h : m₁.extend h₁ = m₂.extend h₂) : i₁ = i₂ := by
  cases m₁ <;> cases m₂ <;> simp [Member.extend] at h
  case root.root     => rfl
  case strict.strict => simp [StrictMember.extend_inj h]
  case root.strict   => exact absurd h.symm $ StrictMember.extend_not_final _ _ _
  case strict.root   => exact absurd h $ StrictMember.extend_not_final _ _ _

def fromLawfulMemUpdate (m : Member c j rtr₂) (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) : 
    Member c j rtr₁ :=
  match m with
  | root => root 
  | strict s => s.fromLawfulMemUpdate u

def fromLawfulUpdate (m : Member c j rtr₂) (u : LawfulUpdate cpt i v rtr₁ rtr₂) : Member c j rtr₁ :=
  match m with
  | root => root
  | strict s => s.fromLawfulUpdate u

def fromEquiv (e : rtr₁ ≈ rtr₂) : (Member cpt i rtr₁) → Member cpt i rtr₂
  | root     => root
  | strict s => s.fromEquiv e

inductive Equivalent [ReactorType β] {rtr₂ : β} : (Member cpt i rtr₁) → (Member cpt i rtr₂) → Prop 
  | root   : Equivalent root root
  | strict : (StrictMember.Equivalent s₁ s₂) → Equivalent (strict s₁) (strict s₂)

namespace Equivalent

instance [ReactorType β] {rtr₂ : β} : HasHEquiv (Member cpt i rtr₁) (Member cpt i rtr₂) where
  HEquiv := Equivalent (cpt := cpt) (i := i) (rtr₁ := rtr₁) (rtr₂ := rtr₂)

theorem refl : (m : Member cpt i rtr) → m ∼ m
  | .root     => root
  | .strict s => strict $ .refl s

theorem symm [ReactorType β] {rtr₂ : β} {m₁ : Member cpt i rtr₁} {m₂ : Member cpt i rtr₂} 
    (e : m₁ ∼ m₂) : m₂ ∼ m₁ := by
  cases m₁ 
  case root => cases m₂; exact root
  case strict => cases cpt <;> cases e <;> exact .strict $ StrictMember.Equivalent.symm ‹_›  

theorem trans [ReactorType β] [ReactorType γ] {rtr₂ : β} {rtr₃ : γ}
    {m₁ : Member cpt i rtr₁} {m₂ : Member cpt i rtr₂} {m₃ : Member cpt i rtr₃}
    (e₁ : m₁ ∼ m₂) (e₂ : m₂ ∼ m₃) : m₁ ∼ m₃ := by
  cases m₁
  case root => cases m₃; exact root
  case strict =>
    cases cpt <;> cases e₁ <;> cases e₂ <;> exact .strict $ StrictMember.Equivalent.trans ‹_› ‹_›  

instance : Equivalence (Equivalent (· : Member cpt i rtr) ·) := 
  { refl, symm, trans }

theorem to_eq {m₁ m₂ : Member cpt i rtr} : (m₁ ∼ m₂) → m₁ = m₂
  | root     => rfl
  | strict e => congr_arg _ $ StrictMember.Equivalent.to_eq e

theorem fromLawfulMemUpdate (u : LawfulMemUpdate cpt i v rtr₁ rtr₂) : 
    (m : Member c j rtr₂) → m ∼ m.fromLawfulMemUpdate u
  | .root     => root
  | .strict s => strict $ .fromLawfulMemUpdate u s 

theorem fromLawfulUpdate (u : LawfulUpdate cpt i v rtr₁ rtr₂) :
    (m : Member c j rtr₂) → m ∼ m.fromLawfulUpdate u
  | .root     => root
  | .strict s => strict $ .fromLawfulUpdate u s 

end Equivalent
end Member

/- ---------------------------------------------------------------------------------------------- -/
namespace Object

variable [ReactorType α] {rtr rtr₁ : α}

theorem «def» : (Object rtr cpt i o) ↔ (∃ m : Member cpt i rtr, m.object = o) where
  mp  | ⟨m⟩    => ⟨m, rfl⟩ 
  mpr | ⟨m, h⟩ => h ▸ ⟨m⟩   

theorem strict_elim {i : ID} : (Object rtr cpt i o) → ∃ (s : StrictMember cpt i rtr), s.object = o
  | ⟨m⟩ => by cases cpt <;> cases m <;> exists ‹_›

theorem not_of_member_isEmpty (h : IsEmpty $ Member cpt i rtr) (o) : ¬Object rtr cpt i o :=
  fun ⟨m⟩ => h.elim m

theorem equiv_exists_object_iff (e : rtr₁ ≈ rtr₂) :
    (∃ o₁, Object rtr₁ cpt i o₁) ↔ (∃ o₂, Object rtr₂ cpt i o₂) where
  mp  | ⟨_, ⟨m⟩⟩ => ⟨_, ⟨m.fromEquiv e⟩⟩
  mpr | ⟨_, ⟨m⟩⟩ => ⟨_, ⟨m.fromEquiv $ Equivalent.symm e⟩⟩
  
end Object

/- ---------------------------------------------------------------------------------------------- -/
namespace UniqueIDs

variable [ReactorType α] {rtr₁ : α}

theorem updated (u : LawfulUpdate cpt i v rtr₁ rtr₂) (h : UniqueIDs rtr₁) : UniqueIDs rtr₂ where
  allEq m₁ m₂ := open Member.Equivalent in
    to_eq $ trans 
      (h.allEq (m₁.fromLawfulUpdate u) (m₂.fromLawfulUpdate u) ▸ fromLawfulUpdate u m₁)
      (symm (fromLawfulUpdate u m₂))

end UniqueIDs
end ReactorType