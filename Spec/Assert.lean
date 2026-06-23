module
public import Init.System.IO
public import Lean.Data.RBTree
public import Lean
public import Lean.Data.RBMap
public import Std.Data.HashSet
public import Lean.Data.RBTree
public import Init.System.IO
public import Lean.Elab.Term
public import Lean.Parser.Term
public import Init.Data.Repr

@[expose] public section

namespace Spec.Assert

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

initialize initialCwd : IO.Ref FilePath ← do
  let cwd ← IO.currentDir
  IO.mkRef cwd

-- Helper for comparing arrays of strings, ignoring order
def _root_.Array.sortedEq (arr1 arr2 : Array String) : Bool :=
  arr1.insertionSort == arr2.insertionSort

-- Assertion helpers
def assertEq (name : String) (expected actual : Array String) : IO Unit := do
  unless actual.sortedEq expected do
    IO.println s!"❌ {name} failed: Expected {reprStr expected}, got {reprStr actual}"
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertBool (name : String) (expected actual : Bool) : IO Unit := do
  unless actual == expected do
    IO.println s!"❌ {name} failed: Expected {expected}, got {actual}"
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertIsNotEmpty (name : String) (actual : Array String) : IO Unit := do
  unless !actual.isEmpty do
    IO.println s!"❌ {name} failed: Expected non-empty array, got empty."
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertIsEmpty (name : String) (actual : Array String) : IO Unit := do
  unless actual.isEmpty do
    IO.println s!"❌ {name} failed: Expected empty array, got {reprStr actual}."
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertThrows (name : String) (ioAction : IO Unit) : IO Unit := do
  let result ← try
    ioAction
    pure none
  catch e =>
    IO.println s!"✅ {name} caught expected error: {e}"
    pure (some e)
  unless result.isSome do
    IO.println s!"❌ {name} failed: Expected an error, but no error was thrown."
    throw <| IO.Error.userError s!"Assertion failed: {name}"

/-- Run `act` inside a fresh temporary directory, restoring the previous working
directory afterwards. Each parallel test gets its own isolated dir. -/
def withinTempDir (act : FilePath → IO α) : IO α := do
  let prev ← initialCwd.get
  -- unique-ish directory name based on a high-resolution timestamp.
  let stamp ← IO.monoNanosNow
  let dir : FilePath := prev / s!".spec-tmp-{stamp}"
  IO.FS.createDirAll dir
  try
    act dir
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()



end Spec.Assert
end
