import ReactorModel.Components

/- REMOVE:
So, ich hab meine Gedanken nochmal ein bisschen sortiert.
So wie ich das sehe befindet sich die `freshID` Funktion in einem Tradeoff zwischen zwei Faktoren:

(1) Wie leicht lässt sich aus dem `resilient` Constraint "ID-Determinismus" ableiten?
(2) Wie sicher sind wir, dass eine `freshID` Funktion mit den gegebenen Constraints überhaupt existiert?

Das Extrem für Faktor (1) wäre die Formulierung von `freshID` mit:

resilient : 
  ∀ {σ₁ σ₂ cmp i rtr₁ rtr₂},
    σ₁ *[Cmp.rtr:i]= rtr₁ →
    σ₂ *[Cmp.rtr:i]= rtr₂ → 
    rtr₁.cmp cmp = rtr₂.cmp cmp → 
    func σ₁ cmp i = func σ₂ cmp i

Hier lässt sich ID-Determinismus sehr leicht ableiten, aber es ist unwahrscheinlich, dass so eine Funktion existiert.

Das Extrem für Faktor (2) wäre keinen `resilient` Constraint zu haben.
Dann existiert die Funktion zwar auf jeden Fall, aber wir können nur ID-Isomorphie zeigen.

Wir brauchen also irgendeinen Constraint der zwischen liegt... dachte ich erst.
Dann ist mir aber aufgefallen, dass jeder `resilient` Constraint am gleichen Problem scheitern könnte wie der obige `resilient` Constraint:
Das Problem ist immer, dass der (top-level) Reactor in den wir eine neue Komponente einfügen wollen vielleicht schon die ID enthält die eigentlich gemäß "naming scheme" der `freshID` Funktion für die neue Komponente angedacht wäre.
D.h. eine `freshID` Funktion die den einen gegebenen `resilient` Constraint einhält kann ohnehin immer nur existieren sofern es einen Mechanismus gibt um für einen "naming-scheme uncompliant" Reactor eine ID zu generieren.
-/

structure Execution.Context.FreshIDFunc where
  func : Reactor → Rooted ID → ID
  -- fresh : ∀ σ i, func σ i ∉ σ.allIDs
  resilient : sorry

open Execution.Context in
structure Execution.Context where
  processedRcns : Time.Tag ⇉ Finset ID
  processedNonempty : processedRcns.nonempty
  freshID : FreshIDFunc

namespace Execution.Context

-- An extensionality theorem for `Context`.
theorem ext_iff {ctx₁ ctx₂ : Context} : 
  ctx₁ = ctx₂ ↔ 
  ctx₁.processedRcns = ctx₂.processedRcns ∧ ctx₁.freshID = ctx₂.freshID := by
  constructor
  case mp => intro h; simp [h]
  case mpr => intro h; cases ctx₁; cases ctx₂; simp [h]

def time (ctx : Context) : Time.Tag :=
  ctx.processedRcns.ids.max' ⟨ctx.processedNonempty.choose, Finmap.ids_def.mpr ctx.processedNonempty.choose_spec⟩

theorem processedRcns_at_time_isSome (ctx : Context) :
  (ctx.processedRcns ctx.time).isSome := by
  simp only [Option.isSome_iff_exists]
  have h : ∀ a, ctx.processedRcns.lookup (time ctx) = some a ↔ some a = ctx.processedRcns.lookup (time ctx) := by
    intro a; constructor <;> (intro h; exact h.symm)
  simp only [h, ←Finmap.ids_def']
  exact Finset.max'_mem _ _

def currentProcessedRcns (ctx : Context) : Finset ID :=
  (ctx.processedRcns ctx.time).get ctx.processedRcns_at_time_isSome

theorem currentProcessedRcns_def (ctx : Context) : some ctx.currentProcessedRcns = ctx.processedRcns ctx.time := by
  simp [currentProcessedRcns, Option.get_some $ ctx.processedRcns ctx.time]

noncomputable def addCurrentProcessed (ctx : Context) (i : ID) : Context := {
  processedRcns := ctx.processedRcns.update ctx.time $ ctx.currentProcessedRcns.insert i,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty,
  freshID := ctx.freshID
}

@[simp]
theorem addCurrentProcessed_preserves_freshID (ctx : Context) (i : ID) : (ctx.addCurrentProcessed i).freshID = ctx.freshID := rfl

theorem addCurrentProcessed_preserves_ctx_past_future (ctx : Context) (i : ID) : ∀ g, g ≠ ctx.time → (ctx.addCurrentProcessed i).processedRcns g = ctx.processedRcns g := by
  intro g h
  simp [addCurrentProcessed, Finmap.update_ne _ h.symm]

theorem addCurrentProcessed_same_time (ctx : Context) (i : ID) : (ctx.addCurrentProcessed i).time = ctx.time := by 
  suffices h : (ctx.addCurrentProcessed i).processedRcns.ids = ctx.processedRcns.ids by 
    simp [time, h]
    sorry
  sorry

theorem addCurrentProcessed_mem_currentProcessedRcns {ctx : Context} {i j : ID} : i ∈ (ctx.addCurrentProcessed j).currentProcessedRcns ↔ (i = j ∨ i ∈ ctx.currentProcessedRcns) := by
  sorry

noncomputable def advanceTime (ctx : Context) (g : Time.Tag) (h : ctx.time < g) : Context := {
  processedRcns := ctx.processedRcns.update' g ∅,
  processedNonempty := ctx.processedRcns.update_nonempty _ _ ctx.processedNonempty,
  freshID := ctx.freshID
}

theorem advanceTime_strictly_increasing (ctx : Context) {g : Time.Tag} (h : ctx.time < g) :
  ctx.time < (ctx.advanceTime g h).time := by
  sorry

end Execution.Context