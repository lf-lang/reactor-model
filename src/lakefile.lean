import Lake
open Lake DSL

package reactor_model where
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "b6afb0dfcaeee607ddd20f38373d2f1419b517c8"
    }
  ]