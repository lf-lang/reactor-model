import Lake
open Lake DSL

package reactor_model where
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "1b6c2fbe04b01ab498cf743d2f4725bc1bb3dcfb"
    }
  ]