import ReactorModel.Components

structure Execution.Context where
  executedRcns : Time.Tag ▸ Finset ID
  nonempty : executedRcns.nonempty

namespace Execution.Context

-- An extensionality theorem for `Context`.
theorem ext_iff {ctx₁ ctx₂ : Context} : ctx₁ = ctx₂ ↔ ctx₁.executedRcns = ctx₂.executedRcns := by
  constructor
  case mp => intro h; simp [h]
  case mpr => intro h; cases ctx₁; cases ctx₂; simp [h]

def time (ctx : Context) : Time.Tag :=
  ctx.executedRcns.ids.max' ⟨ctx.nonempty.choose, Finmap.ids_def.mpr ctx.nonempty.choose_spec⟩

theorem executedRcns_at_time_isSome (ctx : Context) :
  (ctx.executedRcns ctx.time).isSome :=
  sorry

def currentExecutedRcns (ctx : Context) : Finset ID :=
  (ctx.executedRcns ctx.time).get ctx.executedRcns_at_time_isSome

theorem currentExecutedRcns_def (ctx : Context) : some ctx.currentExecutedRcns = ctx.executedRcns ctx.time := by
  sorry

noncomputable def addCurrentExecuted (ctx : Context) (i : ID) : Context := {
  executedRcns := ctx.executedRcns.update ctx.time $ ctx.currentExecutedRcns.insert i,
  nonempty := sorry
}

theorem addCurrentExecuted_same_time (ctx : Context) (i : ID) : (ctx.addCurrentExecuted i).time = ctx.time := by
  sorry

noncomputable def advanceTime (ctx : Context) (g : Time.Tag) (h : ctx.time < g) : Context := {
  executedRcns := ctx.executedRcns.update' g ∅,
  nonempty := sorry
}

theorem advanceTime_strictly_increasing (ctx : Context) (g : Time.Tag) (h : ctx.time < g) :
  ctx.time < (ctx.advanceTime g h).time := by
  sorry

end Execution.Context