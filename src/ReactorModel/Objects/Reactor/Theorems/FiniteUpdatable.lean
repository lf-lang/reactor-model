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

def update' (rtr : α) (cpt : Component.Valued) (v : Value) : α :=
  go rtr cpt v $ Finite.ids rtr cpt
where 
  go (rtr : α) (cpt : Component.Valued) (v : Value) : List ID → α
    | [] => rtr
    | hd :: tl => go (Updatable.update rtr cpt hd v) cpt v tl

variable {rtr : α} 

theorem update'.go_equiv : rtr ≈ update'.go rtr cpt v ids := by
  induction ids generalizing rtr <;> simp [go]
  case nil     => exact .refl _
  case cons hi => exact Equivalent.trans LawfulUpdatable.equiv hi

theorem update'_equiv : rtr ≈ update' rtr cpt v :=
  update'.go_equiv

theorem update'.go_preserves {c : Component.Valued} {o v} 
    (ho : rtr[c][i] = some o) (h : c ≠ cpt ∨ i ∉ ids) : 
    (update'.go rtr cpt v ids)[c][i] = some o := by
  induction ids generalizing rtr o <;> simp_all [go]; cases h
  all_goals
    have e := @LawfulUpdatable.equiv _ cpt ‹_› v _ rtr
    have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
  case cons.inl hd tl hi h _ =>
    simp [hi ho' $ .inl h]
    injection ho' ▸ ho ▸ LawfulUpdatable.obj?_preserved_cpt h
  case cons hd tl hi h _ =>
    push_neg at h
    simp [hi ho' $ .inr h.right]
    injection ho' ▸ ho ▸ LawfulUpdatable.obj?_preserved_id h.left

theorem update'.go_updated {cpt : Component.Valued} {o v} 
    (ho : rtr[cpt][i] = some o) (h : i ∈ ids) : (update'.go rtr cpt v ids)[cpt][i] = some v := by
  induction ids generalizing rtr o <;> simp [go] <;> simp at h; cases h
  all_goals
    try subst ‹_ = _›  
    have e := @LawfulUpdatable.equiv _ cpt ‹_› v _ rtr
    have ⟨_, ho'⟩ := Equivalent.obj?_some_iff e |>.mp ⟨_, ho⟩
  case' cons.inl hd tl hi _ =>
    by_cases ht : i ∈ tl
    case neg => simp [update'.go_preserves ho' (.inr ht), ho' ▸ LawfulUpdatable.obj?_updated, ho]
  all_goals
    have hi := ‹∀ {_} {_}, _›
    exact hi ho' ‹_›

theorem update'_updated : (update' rtr cpt v)[cpt] = rtr[cpt].map (fun _ => v) := by
  ext1 i
  cases ho : rtr[cpt][i] <;> simp [Partial.map_val, ho]
  case some => exact update'.go_updated ho $ mem_ids_iff.mpr ⟨_, ho⟩
  case none => exact Equivalent.obj?_none_iff update'_equiv |>.mp ho

theorem update'_preserves (h : c ≠ cpt) : (update' rtr cpt v)[c] = rtr[c] := by
  ext1 i
  cases ho : rtr[c][i] <;> simp [Partial.map_val, ho]
  case some => exact update'.go_preserves ho (.inl h)
  case none => exact Equivalent.obj?_none_iff update'_equiv |>.mp ho

end FiniteUpdatable
end ReactorType