import Lake
open Lake DSL

package reactor_model where
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "7f7ccfee563a29488274467e0a074b50d44d5fef"
    }
  ]