import Init.Data.Repr
import Init.System.IO
import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Lean.Elab.Term
import Lean.Parser.Term
import Std.Data.HashSet
import Test.NormalizeReturnsIsValidSpec

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def withinTempDir (cont : IO α) : IO α := do
  withTempDir fun tmpDir => do
    IO.Process.setCurrentDir tmpDir
    IO.println s!"⏰ Running in temporary directory: {tmpDir}"
    cont

def runTests (tests : Array (String × (IO Unit))) : IO Unit := do
  let mut successCount := 0
  let totalCount := tests.size
  let originalCwd ← IO.currentDir
  for (name, testFn) in tests do
    IO.println s!"\n--- ⏰ Running Test: {name} ---"
    try
      testFn
      IO.println s!"✅ {name} passed."
      successCount := successCount + 1
    catch e =>
      IO.println s!"❌ {name} failed with error: {e}"
    finally
      IO.Process.setCurrentDir originalCwd
  IO.println s!"\n--- Test Summary ---"
  IO.println s!"Total tests: {totalCount}, Passed: {successCount}, Failed: {totalCount - successCount}"
  unless successCount == totalCount do
    throw <| IO.Error.userError "Some tests failed!"
