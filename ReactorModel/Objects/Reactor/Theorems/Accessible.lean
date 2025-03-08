import ReactorModel.Objects.Reactor.Finite
import ReactorModel.Objects.Reactor.Theorems.Hierarchical
import ReactorModel.Objects.Reactor.Theorems.Finite

noncomputable section

namespace Reactor

class Accessible (α) extends LawfulUpdatable α, Hierarchical α

open Updatable LawfulUpdatable Hierarchical

variable [Accessible α] {rtr : α}

theorem obj?_preserved (h : c ≠ cpt ∨ j ≠ i) : (update rtr cpt i v)[c][j] = rtr[c][j] :=
  lawful rtr cpt i v |>.obj?_preserved h

theorem obj?_preserved_cpt (h : c ≠ cpt := by exact (nomatch ·)) :
    (update rtr cpt i v)[c][j] = rtr[c][j] :=
  obj?_preserved <| .inl h

theorem obj?_preserved_id {c : Component.Valued} (h : j ≠ i) :
    (update rtr cpt i v)[c][j] = rtr[c][j] :=
  obj?_preserved <| .inr h

theorem obj?_updated : (update rtr cpt i v)[cpt][i] = (fun _ => v) <$> rtr[cpt][i] :=
  lawful rtr cpt i v |>.obj?_updated

variable [Finite α]

-- This function has slightly odd behavior. Its intended use is to override all values of a given
-- component type `cpt` with new values given by the map `vs`. When `vs.ids = rtr[cpt].ids` this is
-- exactly what happens. When `vs.ids ≠ rtr[cpt].ids`, the values whose id is not in
-- `rtr[cpt].ids ∩ vs.ids` remain unchanged.
def set (rtr : α) (cpt : Component.Valued) (vs : α✦ ⇀ Value) : α :=
  go rtr cpt vs <| Finite.ids rtr cpt
where
  go (rtr : α) (cpt : Component.Valued) (vs : α✦ ⇀ Value) : List α✦ → α
    | [] => rtr
    | hd :: tl =>
      match vs hd with
      | none   => go rtr cpt vs tl
      | some v => go (Updatable.update rtr cpt hd v) cpt vs tl

omit [Finite α] in
theorem set.go_equiv : rtr ≈ set.go rtr cpt vs ids := by
  induction ids generalizing rtr <;> simp [go]
  case nil     => exact .refl _
  case cons hd _ hi =>
    cases vs hd
    case none => exact hi
    case some => exact Equivalent.trans LawfulUpdatable.equiv hi

theorem set_equiv : rtr ≈ set rtr cpt vs :=
  set.go_equiv

omit [Finite α] in
theorem set.go_preserves {c : Component.Valued} {i o vs}
    (ho : rtr[c][i] = some o) (h : c ≠ cpt ∨ i ∉ ids ∨ vs i = none) :
    (set.go rtr cpt vs ids)[c][i] = some o := by
  induction ids generalizing rtr o <;> simp_all [go]; split <;> cases h <;> try cases ‹_ ∨ _›
  case _ hi _ _ h => exact hi ho <| .inl h
  case _ hi _ _ h => exact hi ho <| .inr <| .inl h.right
  case _ hi _ _ h => exact hi ho <| .inr <| .inr h
  case inl hd tl hi _ v _ h =>
    have e := @LawfulUpdatable.equiv _ cpt v _ rtr ‹_›
    have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
    simp [hi ho' <| .inl h]
    injection ho' ▸ ho ▸ obj?_preserved_cpt h
  case inr.inl hd tl hi _ v _ h =>
    have e := @LawfulUpdatable.equiv _ cpt v _ rtr ‹_›
    have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
    push_neg at h
    simp [hi ho' <| .inr <| .inl h.right]
    injection ho' ▸ ho ▸ obj?_preserved_id h.left
  case inr.inr hd tl hi _ v _ h =>
    have hh : i ≠ hd := by by_contra; simp_all
    have ho' := ho ▸ (@LawfulUpdatable.lawful _ _ rtr cpt hd v).obj?_preserved (c := c) (.inr hh)
    exact hi ho' (.inr <| .inr h)

omit [Finite α] in
theorem set.go_updated {cpt : Component.Valued} {o vs}
    (ho : rtr[cpt][i] = some o) (hv : vs i = some v) (h : i ∈ ids) :
    (set.go rtr cpt vs ids)[cpt][i] = v := by
  induction ids generalizing rtr o v i <;> simp at h; cases h
  case cons.inl tl hi h =>
    subst h
    simp [go, hv]
    have e := @LawfulUpdatable.equiv _ cpt v _ rtr i
    have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
    by_cases ht : i ∈ tl
    case pos => exact hi ho' hv ht
    case neg => simp [set.go_preserves ho' (.inr <| .inl ht), ho' ▸ obj?_updated, ho]
  case cons.inr hd _ hi ht =>
    simp [go]
    split
    · exact hi ho hv ht
    case _ v _ =>
      have e := @LawfulUpdatable.equiv _ cpt v _ rtr hd
      have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
      exact hi ho' hv ht

theorem set_updated' : (set rtr cpt vs)[cpt] = fun i => rtr[cpt][i] >>= (vs i |>.getD ·) := by
  ext1 i
  cases ho : rtr[cpt][i] <;> simp [bind, ho, Option.getD] <;> try split
  · exact Equivalent.obj?_none_iff set_equiv |>.mp ho
  · exact set.go_updated ho ‹_› <| mem_ids_iff.mpr ⟨_, ho⟩
  · exact set.go_preserves ho <| .inr <| .inr ‹_›

theorem set_updated {cpt : Component.Valued} (h : vs.ids = rtr[cpt].ids) :
    (set rtr cpt vs)[cpt] = vs := by
  simp [set_updated', bind, Option.bind]
  ext1 i
  split
  all_goals
    case' _ hn =>
      simp [Partial.ids, Set.ext_iff] at h
      specialize h i
      simp [hn] at h
  · exact Option.eq_none_iff_forall_not_mem.mpr h |>.symm
  · obtain ⟨_, h⟩ := h; simp [h]

theorem set_preserves (h : c ≠ cpt) : (set rtr cpt vs)[c] = rtr[c] := by
  ext1 i
  cases ho : rtr[c][i]
  case some => exact set.go_preserves ho (.inl h)
  case none => exact Equivalent.obj?_none_iff set_equiv |>.mp ho

end Reactor
