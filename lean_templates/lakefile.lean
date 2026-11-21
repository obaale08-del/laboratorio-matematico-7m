import Lake
open Lake DSL

package heptalogo_milennium where
  root := `HeptalogoMain

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
executable heptalogo_main where
  root := `HeptalogoMain
