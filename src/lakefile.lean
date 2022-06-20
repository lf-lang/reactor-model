import Lake
open Lake DSL

package reactor_model where
  defaultFacet := PackageFacet.leanLib
  dependencies := #[
    {
      name := `mathlib
      src := Source.git "https://github.com/leanprover-community/mathlib4.git" "1ac9dea0cdfd0150d1759eef4f76ee0eca5cd108"
    }
  ]