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
public import GlobTest.NormalizeReturnsIsValidSpec
public import LSpec

@[expose] public section

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

/-!
## Test Suite for System.Glob FFI

This test suite creates isolated temporary directories for each test,
creates files within them, runs glob operations, and asserts the results.
-/

-- Helper for comparing arrays of strings, ignoring order
def Array.sortedEq (arr1 arr2 : Array String) : Bool :=
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

/- def assertGlob (pattern : Pattern) (expected : ?a) : IO Unit := -/
/-   assertEq (Pattern.toString pattern) expected (← glob (← IO.Process.setCurrentDir) pattern) -/

end
