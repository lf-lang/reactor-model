import ReactorModel.Execution.Basic

variable {ι υ} [Value υ]

-- TODO: What assumptions are required?
--       E.g. we probably need to require a total order on reactions' priorities.
-- theorem Execution.deterministic {σ σ₁ : Reactor ι υ} {ctx ctx₁ : Execution.Context ι}
  