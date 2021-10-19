macro "unfold " l:many1(ident) : tactic =>
  `(simp only [$l,*])

macro "obtain " t:term " := " h:term : tactic => 
  `(match $h:term with | $t:term => ?_)