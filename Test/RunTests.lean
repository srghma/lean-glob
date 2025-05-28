import Init.System.IO
import Lean.Data.RBTree
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Lean.Parser.Term
import Init.Data.Repr
import Test.NormalizeReturnsIsValidSpec

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def runTests (tests : Array (String × (FilePath → IO Unit))) : IO Unit := do
  let mut successCount := 0
  let totalCount := tests.size
  for (name, testFn) in tests do
    IO.println s!"\n--- Running Test: {name} ---"
    let originalCwd ← IO.currentDir
    try
      -- Execute the test within a temporary directory
      withTempDir (fun tmpDir => do
        IO.println s!"⏰ Running {name} in temporary directory: {tmpDir}"
        IO.Process.setCurrentDir tmpDir
        testFn tmpDir
        IO.Process.setCurrentDir originalCwd)
      IO.println s!"✅ {name} passed."
      successCount := successCount + 1
    catch e =>
      IO.println s!"❌ {name} failed with error: {e}"
      IO.Process.setCurrentDir originalCwd
  IO.println s!"\n--- Test Summary ---"
  IO.println s!"Total tests: {totalCount}, Passed: {successCount}, Failed: {totalCount - successCount}"
  unless successCount == totalCount do
    throw <| IO.Error.userError "Some tests failed!"
