import Lake
open Lake DSL

package reactor_model where
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "2be753a43b2520ef1967a0c5e5a23192b9dc792f"
    }
  ]