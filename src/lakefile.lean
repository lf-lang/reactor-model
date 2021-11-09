import Lake
open Lake DSL

package reactor_model where
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "28111cf310ecb9e90425c922b427ab4d47218bab"
    }
  ]