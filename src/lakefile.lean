import Lake
open Lake DSL

package reactor_model where
  defaultFacet := PackageFacet.oleans
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "dac563e0435386c136c91bc3cc6d9b1edd90376f"
    }
  ]