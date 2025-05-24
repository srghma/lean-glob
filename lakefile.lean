import Lake
open Lake DSL System

-- lake exe graph --to GlobPosix my.pdf --include-lean --include-std --include-deps
/- require importGraph from git "https://github.com/leanprover-community/import-graph.git" @ "main" -/

require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "main" / "regex"
/- require "leanprover-community" / "mathlib" -/
require "leanprover-community" / "batteries" @ git "main"

package glob

@[default_target]
lean_lib Glob where
  srcDir := "lean"

-- lake test
@[test_driver]
lean_exe test where
  srcDir := "test"
  root := `Main
