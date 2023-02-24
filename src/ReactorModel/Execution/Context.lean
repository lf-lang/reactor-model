import ReactorModel.Components

open Classical

@[ext]
structure Execution.Context where
  processedRcns : Time.Tag ⇉ Finset ID -- TODO: Rename this to "history".
  processedNonempty : processedRcns.nonempty

namespace Execution.Context

def tag (ctx : Context) : Time.Tag :=
  ctx.processedRcns.ids.max' ⟨ctx.processedNonempty.choose, Finmap.ids_def.mpr ctx.processedNonempty.choose_spec⟩

theorem processedRcns_at_time_isSome (ctx : Context) : (ctx.processedRcns ctx.tag).isSome := by
  simp only [Option.isSome_iff_exists]
  have h : ∀ a, ctx.processedRcns.lookup (tag ctx) = some a ↔ ctx.processedRcns.lookup (tag ctx) = some a := by
    intro a; constructor <;> (intro h; exact h)
  simp only [h, ←Finmap.ids_def']
  exact Finset.max'_mem _ _

def progress (ctx : Context) : Finset ID :=
  (ctx.processedRcns ctx.tag).get ctx.processedRcns_at_time_isSome

theorem progress_def (ctx : Context) : some ctx.progress = ctx.processedRcns ctx.tag := by
  simp [progress, Option.get_some $ ctx.processedRcns ctx.tag]

-- TODO: Remove the proof condition from this?
noncomputable def advanceTag (ctx : Context) (g : Time.Tag) (_ : ctx.tag < g) : Context := {
  processedRcns := ctx.processedRcns.update' g ∅,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty
}

theorem advanceTag_strictly_increasing (ctx : Context) {g : Time.Tag} (h : ctx.tag < g) :
  ctx.tag < (ctx.advanceTag g h).tag := by
  sorry

theorem advanceTag_progress_empty (ctx : Context) {g : Time.Tag} (h : ctx.tag < g) :
  (ctx.advanceTag g h).progress = ∅ := by
  sorry

noncomputable def record (ctx : Context) (i : ID) : Context := {
  processedRcns := ctx.processedRcns.update ctx.tag $ ctx.progress.insert i,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty
}

theorem record_comm (ctx : Context) (i j : ID) : (ctx.record i).record j = (ctx.record j).record i := by
  sorry

theorem mem_record_progress_self (ctx : Context) (i : ID) : i ∈ (ctx.record i).progress := by
  sorry

theorem record_progress_monotonic {ctx : Context} (j : ID) : 
    (i ∈ ctx.progress) → i ∈ (ctx.record j).progress := by
  sorry

theorem mem_record_progress_iff {ctx : Context} {i j : ID} : 
    i ∈ (ctx.record j).progress ↔ (i = j ∨ i ∈ ctx.progress) := by
  sorry

theorem record_same_tag (ctx : Context) (i : ID) : (ctx.record i).tag = ctx.tag := by 
  suffices h : (ctx.record i).processedRcns.ids = ctx.processedRcns.ids by 
    simp [tag, h]
  sorry

noncomputable def record' (ctx : Context) : List ID → Context
  | [] => ctx
  | hd :: tl => (ctx.record hd).record' tl

theorem record'_cons {ctx : Context} : (ctx.record i).record' l = ctx.record' (i :: l) := rfl

theorem record'_comm (ctx : Context) (l : List ID) (i : ID) :
    (ctx.record' l).record i = (ctx.record i).record' l := by
  induction l generalizing ctx i
  case nil => rfl
  case cons hd tl hi => simp [record', record_comm, hi]

theorem record'_perm_eq {ctx : Context} (h : l₁ ~ l₂) : ctx.record' l₁ = ctx.record' l₂ := by
  induction h generalizing ctx
  case nil     => rfl
  case cons hi => simp [record', hi]
  case swap    => simp [record', record_comm]
  case trans   => simp_all

theorem record'_progress_monotonic {ctx : Context} (l : List ID) (h : i ∈ ctx.progress) :
    i ∈ (ctx.record' l).progress := by
  induction l generalizing ctx i
  case nil => assumption
  case cons hd _ hi => exact hi $ record_progress_monotonic hd h

theorem record'_cons_progress_monotonic {ctx : Context} (h : i ∈ (ctx.record' tl).progress) : 
    i ∈ (ctx.record' $ hd :: tl).progress := by
  simp [record', ←record'_comm, record_progress_monotonic _ h]
  
theorem mem_list_to_mem_record'_progress {ctx : Context} (h : i ∈ l) : 
    i ∈ (ctx.record' l).progress := by
  induction l
  case nil => contradiction
  case cons hd tl hi =>
    cases h
    case head => exact record'_progress_monotonic tl $ ctx.mem_record_progress_self i
    case tail h => exact record'_cons_progress_monotonic $ hi h

theorem mem_record'_progress_to_mem_progress_or_mem_list {ctx : Context} :
    i ∈ (ctx.record' l).progress → (i ∈ ctx.progress ∨ i ∈ l) := by
  sorry

theorem mem_record'_progress_iff (ctx : Context) (l : List ID) (i : ID) :
    i ∈ (ctx.record' l).progress ↔ (i ∈ ctx.progress ∨ i ∈ l) where
  mp := mem_record'_progress_to_mem_progress_or_mem_list
  mpr 
    | .inl h => record'_progress_monotonic l h
    | .inr h => mem_list_to_mem_record'_progress h

end Execution.Context