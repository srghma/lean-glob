import Lake
open Lake DSL System

-- lake exe graph --to GlobPosix my.pdf --include-lean --include-std --include-deps
/- require importGraph from git "https://github.com/leanprover-community/import-graph.git" @ "main" -/

-- require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "main" / "regex"
-- require "leanprover-community" / "mathlib"
require "leanprover-community" / "batteries" @ git "main"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "main"
require aesop from git "https://github.com/leanprover-community/aesop"
require LSpec from git "https://github.com/argumentcomputer/LSpec"

package glob

-- TODO: comment me out
/- package glob { -/
/-   moreLinkArgs := #[ -/
/-     "-L./.lake/packages/LeanCopilot/.lake/build/lib", -/
/-     "-lctranslate2" -/
/-   ] -/
/- } -/

@[default_target]
lean_lib Glob {
  roots := #[`Glob]
  defaultFacets := #[LeanLib.sharedFacet]
}


/- @[default_target] -/
/- lean_lib Glob where -/
/-   srcDir := "lean" -/

lean_lib Test {
}

-- lake test
@[test_driver]
lean_exe test where
  root := `Test.Main
  supportInterpreter := true
