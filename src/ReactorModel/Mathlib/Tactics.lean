macro "exists " t:term : tactic =>
  `(apply Exists.intro $t)

macro "unfold " l:many1(ident) : tactic =>
  `(simp only [$l,*])

-- https://leanprover.zulipchat.com/#narrow/stream/270676-lean4/topic/Collapse.20cases
syntax "case' " ((ident <|> "_")*),* " => " tacticSeq : tactic
macro_rules
  | `(tactic| case' $[$xs:ident*],* => $tac) => do
    let tacs ← xs.mapM fun xs => `(tactic| case $(xs[0]) $(xs[1:])* => $tac)
    `(tactic| ($[$tacs]*))