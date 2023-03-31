import ReactorModel.Objects.Reactor.ReactorType.Basic

namespace ReactorType

-- The relation expresses that `rtr₁` is nested in `rtr₂`.
abbrev Nested [ReactorType α] (rtr₁ rtr₂ : α) : Prop :=
  ∃ i, nest rtr₂ i = some rtr₁

protected class WellFounded (α) extends Extensional α where
  wf : WellFounded $ Nested (α := α)

namespace WellFounded

theorem induction [ReactorType.WellFounded α] {motive : α → Prop} 
    (nest : ∀ rtr, (∀ n, (∃ i, nest rtr i = some n) → motive n) → motive rtr) : ∀ rtr, motive rtr := 
  (wf.induction · nest)

instance [Extensional α] [b : ReactorType.WellFounded β] [c : LawfulCoe α β] : 
    ReactorType.WellFounded α where
  wf := by
    suffices h : InvImage Nested c.coe = Nested from h ▸ InvImage.wf c.coe b.wf
    funext rtr₁ rtr₂
    simp [Nested, InvImage, c.nest', Partial.map_val]
    exact ⟨fun ⟨_, ⟨_, hn, h⟩⟩ => ⟨_, c.inj h ▸ hn⟩, fun ⟨i, h⟩ => ⟨i, rtr₁, by simp [h]⟩⟩  

end WellFounded

@[refl]
theorem Member.Equivalent.refl [ReactorType.WellFounded α] {rtr : α} {m : Member cpt i rtr} : 
    Equivalent m m := by
  induction rtr using ReactorType.WellFounded.induction
  case nest hi =>
    cases m
    case final  => exact .final
    case nest h => exact .nest _ _ (hi _ ⟨_, h⟩)

namespace ReactorType