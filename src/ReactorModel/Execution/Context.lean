import ReactorModel.Components

open Time Classical

structure Execution.Context (ι) where
  executedRcns : Time.Tag ▸ Finset ι
  nonempty : executedRcns.nonempty


namespace Execution.Context

variable {ι υ} [Value υ]

def time (ctx : Context ι) : Time.Tag :=
  ctx.executedRcns.ids.min' ⟨ctx.nonempty.choose, Finmap.ids_def.mpr ctx.nonempty.choose_spec⟩

theorem executedRcns_at_time_isSome (ctx : Context ι) :
  (ctx.executedRcns ctx.time).isSome :=
  sorry

def currentExecutedRcns (ctx : Context ι) : Finset ι :=
  (ctx.executedRcns ctx.time).get ctx.executedRcns_at_time_isSome

noncomputable def addCurrentExecuted (ctx : Context ι) (i : ι) : Context ι := {
  executedRcns := ctx.executedRcns.update ctx.time $ ctx.currentExecutedRcns.insert i,
  nonempty := sorry
}

noncomputable def advanceTime (ctx : Context ι) {g : Time.Tag} (h : ctx.time < g) : Context ι := {
  executedRcns := ctx.executedRcns.update' g ∅,
  nonempty := sorry
}

lemma identicalExecuted {ctx₁ ctx₂ : Context ι} : ctx₁.executedRcns = ctx₂.executedRcns → ctx₁ = ctx₂ :=
sorry

lemma currentIdentical {ctx₁ ctx₂ : Context ι} : ctx₁.currentExecutedRcns = ctx₂.currentExecutedRcns → ctx₁.time = ctx₂.time → ctx₁ = ctx₂ :=
sorry

end Execution.Context