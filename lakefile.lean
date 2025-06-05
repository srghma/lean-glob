import Lake
open Lake DSL System

-- lake exe graph --to GlobPosix my.pdf --include-lean --include-std --include-deps
/- require importGraph from git "https://github.com/leanprover-community/import-graph.git" @ "main" -/
require LeanSpec from git "https://github.com/srghma/lean-spec.git" @ "main"

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
  needs := #[`@/updateTestMain]
  -- globs := #[`Test].map Glob.andSubmodules -- doesn't do anything
  -- supportInterpreter := true

-- script setupscript := do
--   IO.println "generating import list"
--   return 0

target updateTestMain : Unit := do
  IO.println "generating import list"

  -- Create the Test directory if it doesn't exist
  let testDir : System.FilePath := "Test"
  if !(← testDir.pathExists) then IO.FS.createDirAll testDir

  -- Generate the Test/Main.lean file with imports
  let mainContent :=
  "import LSpec

  def main : IO Unit := do
    IO.println \"running test1\"
    -- Add your test logic here
  "
  IO.FS.writeFile (testDir / "Main.lean") mainContent

  IO.println "Generated Test/Main.lean"

  return .nil

-- Convenience scripts using the utilities
script import_all do
  -- LeanSpec.generateImportFile "Glob" "Glob.lean"
  return 0

script import_all? do
  -- if ← LeanSpec.checkImportFile "Glob" "Glob.lean" then
  --   return 0
  -- else
    IO.eprintln "Invalid import list in 'Glob.lean'"
    IO.eprintln "Try running 'lake run import_all'"
    return 1
