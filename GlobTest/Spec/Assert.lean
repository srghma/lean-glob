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
public import Glob.NonWF.Types
public import LSpec
public import Glob.WF.IO

@[expose] public section

namespace GlobTest.Spec.Assert

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)
open NonEmpty.List

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
  let prev ← IO.currentDir
  -- unique-ish directory name based on a high-resolution timestamp.
  let stamp ← IO.monoNanosNow
  let dir : FilePath := prev / s!".spec-tmp-{stamp}"
  IO.FS.createDirAll dir
  try
    act dir
  finally
    try IO.FS.removeDirAll dir catch _ => pure ()



def assertAreEqualAndReturnFirst (a : PatternValidated) (b : List PatternSegmentNonWF) : PatternValidated :=
  if a.pattern == b then a
  else panic! s!"assertAreEqualAndReturnFirst failed: {repr a} != {repr b}"

def assertGlob (tmpDir : FilePath) (pattern : PatternValidated) (expected : Array String) : IO Unit := do
  match NonEmptyList.fromList? pattern.pattern with
  | some nel =>
    let actual ← globFS tmpDir pattern
    assertEq s!"assertGlob {nel}" expected actual
  | none => throw (IO.userError "Pattern cannot be empty")

def assertGlobMany (tmpDir : FilePath) (patterns : NonEmptyList PatternValidated) (expected : Array String) : IO Unit := do
  let mut actual := #[]
  for p in patterns.toList do
    let res ← globFS tmpDir p
    for r in res do
      if !actual.contains r then
        actual := actual.push r
  assertEq s!"assertGlobMany" expected actual



end GlobTest.Spec.Assert
end
