import Lake
open Lake DSL

package reactor_model

lean_lib ReactorModel

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"@"0285b69b1fd0fa0f63"

-- https://github.com/leanprover/doc-gen4#usage
-- meta if get_config? env = some "dev" then 
-- require «doc-gen4» from git "https://github.com/leanprover/doc-gen4"@"master"