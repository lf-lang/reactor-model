import Lean
open Lean

macro "exists " t:term : tactic =>
  `(apply Exists.intro $t)

syntax "case' " (Lean.binderIdent*),* " => " tacticSeq : tactic
macro_rules
  | `(tactic| case' $[$xs*],* => $tac) => do
    let tacs ← xs.mapM fun xs => `(tactic| case $(xs[0]!) $(xs[1:])* => $tac)
    `(tactic| ($[$tacs]*))