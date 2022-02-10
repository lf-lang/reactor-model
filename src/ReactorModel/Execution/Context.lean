import ReactorModel.Components

structure Execution.Context (ι) where
  executedRcns : Time.Tag ▸ Finset ι
  nonempty : executedRcns.nonempty

namespace Execution.Context

variable {ι υ} [Value υ]

-- An extensionality theorem for `Context`.
theorem ext_iff {ctx₁ ctx₂ : Context ι} : ctx₁ = ctx₂ ↔ ctx₁.executedRcns = ctx₂.executedRcns := by
  constructor
  case mp => intro h; simp [h]
  case mpr => intro h; cases ctx₁; cases ctx₂; simp [h]

def time (ctx : Context ι) : Time.Tag :=
  ctx.executedRcns.ids.max' ⟨ctx.nonempty.choose, Finmap.ids_def.mpr ctx.nonempty.choose_spec⟩

theorem executedRcns_at_time_isSome (ctx : Context ι) :
  (ctx.executedRcns ctx.time).isSome :=
  sorry

def currentExecutedRcns (ctx : Context ι) : Finset ι :=
  (ctx.executedRcns ctx.time).get ctx.executedRcns_at_time_isSome

theorem currentExecutedRcns_def (ctx : Context ι) : some ctx.currentExecutedRcns = ctx.executedRcns ctx.time := by
  sorry

noncomputable def addCurrentExecuted (ctx : Context ι) (i : ι) : Context ι := {
  executedRcns := ctx.executedRcns.update ctx.time $ ctx.currentExecutedRcns.insert i,
  nonempty := sorry
}

theorem addCurrentExecuted_same_time (ctx : Context ι) (i : ι) : (ctx.addCurrentExecuted i).time = ctx.time := by
  sorry

noncomputable def advanceTime (ctx : Context ι) (g : Time.Tag) (h : ctx.time < g) : Context ι := {
  executedRcns := ctx.executedRcns.update' g ∅,
  nonempty := sorry
}

theorem advanceTime_strictly_increasing (ctx : Context ι) (g : Time.Tag) (h : ctx.time < g) :
  ctx.time < (ctx.advanceTime g h).time := by
  sorry

end Execution.Context