import ReactorModel.Objects.Reactor.Practical
import ReactorModel.Objects.Reactor.Theorems.Finite
import ReactorModel.Objects.Reactor.Theorems.Indexable
import ReactorModel.Objects.Reactor.Theorems.Accessible

noncomputable section

namespace ReactorType

class FiniteUpdatable (α) extends Finite α, LawfulUpdatable α

instance [FiniteUpdatable α] : Accessible α where
  unique_ids := Indexable.unique_ids

namespace FiniteUpdatable

variable [FiniteUpdatable α]

-- This function has slightly odd behavior. Its intended use is to override all values of a given
-- component type `cpt` with new values given by the map `vs`. When `vs.ids = rtr[cpt].ids` this is
-- exactly what happens. When `vs.ids ≠ rtr[cpt].ids`, the values whose id is not in 
-- `rtr[cpt].ids ∩ vs.ids` remain unchanged.
def set (rtr : α) (cpt : Component.Valued) (vs : ID ⇀ Value) : α :=
  go rtr cpt vs $ Finite.ids rtr cpt
where 
  go (rtr : α) (cpt : Component.Valued) (vs : ID ⇀ Value) : List ID → α
    | [] => rtr
    | hd :: tl => 
      match vs hd with
      | none   => go rtr cpt vs tl
      | some v => go (Updatable.update rtr cpt hd v) cpt vs tl

variable {rtr : α} 

theorem set.go_equiv : rtr ≈ set.go rtr cpt vs ids := by
  induction ids generalizing rtr <;> simp [go]
  case nil     => exact .refl _
  case cons hd _ hi => 
    cases vs hd 
    case none => exact hi
    case some => exact Equivalent.trans LawfulUpdatable.equiv hi

theorem set_equiv : rtr ≈ set rtr cpt vs :=
  set.go_equiv

theorem set.go_preserves {c : Component.Valued} {o vs} 
    (ho : rtr[c][i] = some o) (h : c ≠ cpt ∨ i ∉ ids ∨ vs i = none) : 
    (set.go rtr cpt vs ids)[c][i] = some o := by
  induction ids generalizing rtr o <;> simp_all [go]; split <;> cases h <;> try cases ‹_ ∨ _›    
  case _ hi _ _ h => exact hi ho $ .inl h
  case _ hi _ _ h => exact hi ho $ .inr $ .inl (not_or.mp h).right
  case _ hi _ _ h => exact hi ho $ .inr $ .inr h
  all_goals
    case' _ hi _ v _ _ => 
      -- TODO: Perhaps you need to do this later, so that we're not fixed on `v`.
      have e := @LawfulUpdatable.equiv _ cpt ‹_› v _ rtr
      have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
  case inl hd tl _ _ h _ =>
    simp [hi ho' $ .inl h]
    injection ho' ▸ ho ▸ LawfulUpdatable.obj?_preserved_cpt h
  case inr.inl hd tl _ _ h _ =>
    push_neg at h
    simp [hi ho' $ .inr $ .inl h.right]
    injection ho' ▸ ho ▸ LawfulUpdatable.obj?_preserved_id h.left
  case inr.inr hd tl _ _ h _ =>
    sorry

theorem set.go_updated {cpt : Component.Valued} {o vs} 
    (ho : rtr[cpt][i] = some o) (hv : vs i = some v) (h : i ∈ ids) : 
    (set.go rtr cpt vs ids)[cpt][i] = v := by
  induction ids generalizing rtr o v i <;> simp [go] <;> simp at h; cases h
  all_goals
    try subst ‹_ = _›  
    simp [hv]
    -- TODO: Perhaps you need to do this later, so that we're not fixed on `v`.
    have e := @LawfulUpdatable.equiv _ cpt ‹_› v _ rtr
    have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
  case' cons.inl hd tl hi _ =>
    by_cases ht : i ∈ tl
    case neg => simp [set.go_preserves ho' (.inr $ .inl ht), ho' ▸ LawfulUpdatable.obj?_updated, ho]
  all_goals
    have hi := ‹∀ {_} {_}, _›
    try split
    try exact hi ‹_› hv ‹_›
  · sorry 

theorem set_updated : (set rtr cpt vs)[cpt] = fun i => rtr[cpt][i] >>= (vs i |>.getD ·) := by
  ext1 i
  cases ho : rtr[cpt][i] <;> simp [bind, ho, Option.getD] <;> try split
  · exact Equivalent.obj?_none_iff set_equiv |>.mp ho
  · exact set.go_updated ho ‹_› $ mem_ids_iff.mpr ⟨_, ho⟩
  · exact set.go_preserves ho $ .inr $ .inr ‹_›

theorem set_updated' {cpt : Component.Valued} (h : vs.ids = rtr[cpt].ids) : 
    (set rtr cpt vs)[cpt] = vs := by
  sorry

theorem set_preserves (h : c ≠ cpt) : (set rtr cpt vs)[c] = rtr[c] := by
  ext1 i
  cases ho : rtr[c][i] <;> simp [Partial.map_val, ho]
  case some => exact set.go_preserves ho (.inl h)
  case none => exact Equivalent.obj?_none_iff set_equiv |>.mp ho

end FiniteUpdatable
end ReactorType