import Lake
open Lake DSL

package turing_verifier where

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

lean_lib TuringVerifier

@[default_target]
lean_exe turing_verifier where
  root := `Main
