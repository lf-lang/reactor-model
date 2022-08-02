import ReactorModel.Components

@[ext]
structure Execution.Context where
  processedRcns : Time.Tag ⇉ Finset ID
  processedNonempty : processedRcns.nonempty

namespace Execution.Context

def tag (ctx : Context) : Time.Tag :=
  ctx.processedRcns.ids.max' ⟨ctx.processedNonempty.choose, Finmap.ids_def.mpr ctx.processedNonempty.choose_spec⟩

theorem processedRcns_at_time_isSome (ctx : Context) :
  (ctx.processedRcns ctx.tag).isSome := by
  simp only [Option.isSome_iff_exists]
  have h : ∀ a, ctx.processedRcns.lookup (tag ctx) = some a ↔ ctx.processedRcns.lookup (tag ctx) = some a := by
    intro a; constructor <;> (intro h; exact h)
  simp only [h, ←Finmap.ids_def']
  exact Finset.max'_mem _ _

def currentProcessedRcns (ctx : Context) : Finset ID :=
  (ctx.processedRcns ctx.tag).get ctx.processedRcns_at_time_isSome

theorem currentProcessedRcns_def (ctx : Context) : some ctx.currentProcessedRcns = ctx.processedRcns ctx.tag := by
  simp [currentProcessedRcns, Option.get_some $ ctx.processedRcns ctx.tag]

noncomputable def addCurrentProcessed (ctx : Context) (i : ID) : Context := {
  processedRcns := ctx.processedRcns.update ctx.tag $ ctx.currentProcessedRcns.insert i,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty
}

noncomputable def addCurrentProcessed' (ctx : Context) : List ID → Context
  | [] => ctx
  | hd :: tl => (ctx.addCurrentProcessed hd).addCurrentProcessed' tl

theorem addCurrentProcessed_preserves_ctx_past_future (ctx : Context) (i : ID) : ∀ g, g ≠ ctx.tag → (ctx.addCurrentProcessed i).processedRcns g = ctx.processedRcns g := by
  intro g h
  simp [addCurrentProcessed, Finmap.update_ne _ h.symm]

theorem addCurrentProcessed_same_tag (ctx : Context) (i : ID) : (ctx.addCurrentProcessed i).tag = ctx.tag := by 
  suffices h : (ctx.addCurrentProcessed i).processedRcns.ids = ctx.processedRcns.ids by 
    simp [tag, h]
  sorry

theorem addCurrentProcessed_mem_currentProcessedRcns {ctx : Context} {i j : ID} : i ∈ (ctx.addCurrentProcessed j).currentProcessedRcns ↔ (i = j ∨ i ∈ ctx.currentProcessedRcns) := by
  sorry

noncomputable def advanceTag (ctx : Context) (g : Time.Tag) (h : ctx.tag < g) : Context := {
  processedRcns := ctx.processedRcns.update' g ∅,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty
}

theorem advanceTag_strictly_increasing (ctx : Context) {g : Time.Tag} (h : ctx.tag < g) :
  ctx.tag < (ctx.advanceTag g h).tag := by
  sorry

end Execution.Context