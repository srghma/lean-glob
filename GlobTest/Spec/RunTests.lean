module
public import Init.Data.Repr
public import Init.System.IO
public import Lean
public import Lean.Data.RBMap
public import Lean.Data.RBTree
public import Lean.Elab.Term
public import Lean.Parser.Term
public import Std.Data.HashSet
public import GlobTest.NormalizeReturnsIsValidSpec

@[expose] public section

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
    IO.println s!"
--- ⏰ Running Test: {name} ---"
    try
      testFn
      IO.println s!"✅ {name} passed."
      successCount := successCount + 1
    catch e =>
      IO.println s!"❌ {name} failed with error: {e}"
    finally
      IO.Process.setCurrentDir originalCwd
  IO.println s!"
--- Test Summary ---"
  IO.println s!"Total tests: {totalCount}, Passed: {successCount}, Failed: {totalCount - successCount}"
  unless successCount == totalCount do
    throw <| IO.Error.userError "Some tests failed!"

end
