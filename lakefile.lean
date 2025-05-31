import Lake
open Lake DSL System

-- lake exe graph --to GlobPosix my.pdf --include-lean --include-std --include-deps
/- require importGraph from git "https://github.com/leanprover-community/import-graph.git" @ "main" -/

require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "main" / "regex"
-- require "leanprover-community" / "mathlib"
require "leanprover-community" / "batteries" @ git "main"
-- require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "main"
require aesop from git "https://github.com/leanprover-community/aesop"
require LSpec from git "https://github.com/argumentcomputer/LSpec"

package glob

-- NOTE: only for LeanCopilot
/-
package glob {
  moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}
-/

@[default_target]
lean_lib Glob {
  roots := #[`Glob]
  -- srcDir := "lean"
  -- defaultFacets := #[LeanLib.sharedFacet]
  globs := #[
    `Glob,
    -- `Pathy
    -- `Test.Main -- disable me
  ].map Glob.andSubmodules -- how to make `lake build` build modules even if they are not imported in top level?
}

lean_lib Test {
  globs := #[`Test].map Glob.andSubmodules -- doesn't do anything
}

lean_lib Pathy {
  -- globs := #[`Pathy].map Glob.andSubmodules -- doesnt do anything
}

-- lake test
@[test_driver]
lean_exe test where
  root := `Test.Main
  -- globs := #[`Test].map Glob.andSubmodules -- doesn't do anything
  -- supportInterpreter := true
