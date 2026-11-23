import Lake
open Lake DSL

package petruska_fenix where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.14.0"

@[default_target]
lean_lib LeanTemplates where
  srcDir := "lean_templates"
  roots := #[`ReductionMini, `ReductionTransitivity]
