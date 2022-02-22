import ReactorModel.Components

structure Execution.Context where
  executedRcns : Time.Tag ▸ Finset ID
  execedNonempty : executedRcns.nonempty
  freshID : Reactor → ID   
  freshIDCorrect : ∀ σ cmp, freshID σ ∉ σ.ids cmp

namespace Execution.Context

-- An extensionality theorem for `Context`.
theorem ext_iff {ctx₁ ctx₂ : Context} : 
  ctx₁ = ctx₂ ↔ 
  ctx₁.executedRcns = ctx₂.executedRcns ∧ ctx₁.freshID = ctx₂.freshID := by
  constructor
  case mp => intro h; simp [h]
  case mpr => intro h; cases ctx₁; cases ctx₂; simp [h]

def time (ctx : Context) : Time.Tag :=
  ctx.executedRcns.ids.max' ⟨ctx.execedNonempty.choose, Finmap.ids_def.mpr ctx.execedNonempty.choose_spec⟩

theorem executedRcns_at_time_isSome (ctx : Context) :
  (ctx.executedRcns ctx.time).isSome := by
  simp only [Option.isSome_iff_exists]
  have h : ∀ a, ctx.executedRcns.lookup (time ctx) = some a ↔ some a = ctx.executedRcns.lookup (time ctx) := by
    intro a; constructor <;> (intro h; exact h.symm)
  simp only [h, ←Finmap.ids_def']
  exact Finset.max'_mem _ _

def currentExecutedRcns (ctx : Context) : Finset ID :=
  (ctx.executedRcns ctx.time).get ctx.executedRcns_at_time_isSome

theorem currentExecutedRcns_def (ctx : Context) : some ctx.currentExecutedRcns = ctx.executedRcns ctx.time := by
  simp [currentExecutedRcns, Option.get_some $ ctx.executedRcns ctx.time]

noncomputable def addCurrentExecuted (ctx : Context) (i : ID) : Context := {
  executedRcns := ctx.executedRcns.update ctx.time $ ctx.currentExecutedRcns.insert i,
  execedNonempty := ctx.executedRcns.update_nonempty _ _ ctx.execedNonempty,
  freshID := ctx.freshID,
  freshIDCorrect := ctx.freshIDCorrect
}

theorem addCurrentExecuted_same_time (ctx : Context) (i : ID) : (ctx.addCurrentExecuted i).time = ctx.time := by 
  suffices h : (ctx.addCurrentExecuted i).executedRcns.ids = ctx.executedRcns.ids by 
    simp [time, h]
    sorry
  sorry

noncomputable def advanceTime (ctx : Context) (g : Time.Tag) (h : ctx.time < g) : Context := {
  executedRcns := ctx.executedRcns.update' g ∅,
  execedNonempty := ctx.executedRcns.update_nonempty _ _ ctx.execedNonempty,
  freshID := ctx.freshID,
  freshIDCorrect := ctx.freshIDCorrect
}

theorem advanceTime_strictly_increasing (ctx : Context) (g : Time.Tag) (h : ctx.time < g) :
  ctx.time < (ctx.advanceTime g h).time := by
  sorry

end Execution.Context