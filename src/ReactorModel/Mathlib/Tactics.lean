import Lean
open Lean

macro "exists " t:term : tactic =>
  `(apply Exists.intro $t)

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Collapse.20cases 
syntax "case' " ((ident <|> "_")*),* " => " tacticSeq : tactic
macro_rules
  | `(tactic| case' $[$xs:ident],* => $tac) => do
    let hd : TSyntax `Lean.binderIdent := TSyntax.mk xs[0]!.raw
    let tl : List $ TSyntax `Lean.binderIdent := xs.data[1:0].map fun s => TSyntax.mk s.raw
    let tacs ← xs.mapM fun xs => `(tactic| case $(hd) $(xs[1:])* => $tac)
    `(tactic| ($[$tacs]*))