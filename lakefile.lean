import Lake

open Lake DSL

package categories

lean_lib Categories

require Mathlib from git "https://github.com/leanprover-community/mathlib4" @ "master"

@[default_target]
lean_exe categories {
  root := `Main
}
