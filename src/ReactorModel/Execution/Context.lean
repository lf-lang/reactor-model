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

def progress (ctx : Context) : Finset ID :=
  (ctx.processedRcns ctx.tag).get ctx.processedRcns_at_time_isSome

theorem progress_def (ctx : Context) : some ctx.progress = ctx.processedRcns ctx.tag := by
  simp [progress, Option.get_some $ ctx.processedRcns ctx.tag]

noncomputable def addCurrentProcessed (ctx : Context) (i : ID) : Context := {
  processedRcns := ctx.processedRcns.update ctx.tag $ ctx.progress.insert i,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty
}

noncomputable def process (ctx : Context) : List ID → Context
  | [] => ctx
  | hd :: tl => (ctx.addCurrentProcessed hd).process tl

noncomputable def mark (ctx : Context) : Finset Tag → Context :=
  sorry

theorem process_perm_eq {ctx : Context} {l₁ l₂ : List ID} : 
    (l₁ ~ l₂) → ctx.process l₁ = ctx.process l₂ := 
  sorry

theorem addCurrentProcessed_preserves_ctx_past_future (ctx : Context) (i : ID) : ∀ g, g ≠ ctx.tag → (ctx.addCurrentProcessed i).processedRcns g = ctx.processedRcns g := by
  intro g h
  simp [addCurrentProcessed, Finmap.update_ne _ h.symm]

theorem addCurrentProcessed_same_tag (ctx : Context) (i : ID) : (ctx.addCurrentProcessed i).tag = ctx.tag := by 
  suffices h : (ctx.addCurrentProcessed i).processedRcns.ids = ctx.processedRcns.ids by 
    simp [tag, h]
  sorry

theorem addCurrentProcessed_mem_progress {ctx : Context} {i j : ID} : i ∈ (ctx.addCurrentProcessed j).progress ↔ (i = j ∨ i ∈ ctx.progress) := by
  sorry

noncomputable def advanceTag (ctx : Context) (g : Time.Tag) (h : ctx.tag < g) : Context := {
  processedRcns := ctx.processedRcns.update' g ∅,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty
}

theorem advanceTag_strictly_increasing (ctx : Context) {g : Time.Tag} (h : ctx.tag < g) :
  ctx.tag < (ctx.advanceTag g h).tag := by
  sorry

theorem advanceTag_progress_empty (ctx : Context) {g : Time.Tag} (h : ctx.tag < g) :
  (ctx.advanceTag g h).progress = ∅ := by
  sorry

end Execution.Context