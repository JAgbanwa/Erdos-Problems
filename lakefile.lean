import Lake
open Lake DSL

package «ErdosProblems» where
  version := {major := 0, minor := 0, patch := 1}
  lintDriver := "batteries/runLinter"
  lintDriverArgs := #["ErdosProblems"]

require mathlib from git "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib ErdosProblems
