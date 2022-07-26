import ReactorModel.Execution

open Classical

-- IDEA:
-- Is it simpler to express this notion somehow by first defining a function that collapses
-- "absorbed" changes and then require the resulting lists be permutations of eachother
-- (this won't work for actions, but will for ports and states)?
-- We could then also prove a "small" lemma first, that states that the collapsed list produces
-- the same ChangeList result as the non-collapsed one.
-- Then we can use that lemma to show that ChangeListEquiv lists produce equal
-- ChangeList results.
structure ChangeListEquiv (cs₁ cs₂ : List Change) : Prop where
  ports   : ∀ i,   cs₁.lastSome? (·.portValue? i)     = cs₂.lastSome? (·.portValue? i)
  state   : ∀ i,   cs₁.lastSome? (·.stateValue? i)    = cs₂.lastSome? (·.stateValue? i)
  actions : ∀ i t, cs₁.filterMap (·.actionValue? i t) = cs₂.filterMap (·.actionValue? i t)
  -- NOTE: Mutations are currently noops, and can therefore be ignored.

notation cs₁:max " ⋈ " cs₂:max => ChangeListEquiv cs₁ cs₂