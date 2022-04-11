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
  fresh : ∀ σ i, func σ i ∉ σ.allIDs
  resilient : 
    ∀ {σ₁ σ₂ i rtr₁ rtr₂},
      σ₁ %[Cmp.rtr:i]= σ₂ →       
      σ₁ *[Cmp.rtr:i]= rtr₁ →
      σ₂ *[Cmp.rtr:i]= rtr₂ → 
      rtr₁.allIDs = rtr₂.allIDs → 
      func σ₁ i = func σ₂ i

open Execution.Context in
structure Execution.Context where
  executedRcns : Time.Tag ▸ Finset ID
  execedNonempty : executedRcns.nonempty
  freshID : FreshIDFunc

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
  freshID := ctx.freshID
}

@[simp]
theorem addCurrentExecuted_preserves_freshID (ctx : Context) (i : ID) : (ctx.addCurrentExecuted i).freshID = ctx.freshID := rfl

theorem addCurrentExecuted_preserves_ctx_past_future (ctx : Context) (i : ID) : ∀ g, g ≠ ctx.time → (ctx.addCurrentExecuted i).executedRcns g = ctx.executedRcns g := by
  intro g h
  simp [addCurrentExecuted, Finmap.update_ne _ h.symm]

theorem addCurrentExecuted_same_time (ctx : Context) (i : ID) : (ctx.addCurrentExecuted i).time = ctx.time := by 
  suffices h : (ctx.addCurrentExecuted i).executedRcns.ids = ctx.executedRcns.ids by 
    simp [time, h]
    sorry
  sorry

noncomputable def advanceTime (ctx : Context) (g : Time.Tag) (h : ctx.time < g) : Context := {
  executedRcns := ctx.executedRcns.update' g ∅,
  execedNonempty := ctx.executedRcns.update_nonempty _ _ ctx.execedNonempty,
  freshID := ctx.freshID
}

theorem advanceTime_strictly_increasing (ctx : Context) (g : Time.Tag) (h : ctx.time < g) :
  ctx.time < (ctx.advanceTime g h).time := by
  sorry

end Execution.Context