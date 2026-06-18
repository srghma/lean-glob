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
public import GlobTest.FileFinder

@[expose] public section

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)
open NonEmpty.List

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

partial def matchSegments (pattern : List PatternSegmentNonWF) (path : List String) : Bool :=
  match pattern, path with
  | [], [] => true
  | [], _ => false
  | PatternSegmentNonWF.doubleStar :: ps, [] => matchSegments ps []
  | _ :: _, [] => false
  | PatternSegmentNonWF.doubleStar :: ps, x :: xs =>
      matchSegments ps (x :: xs) || matchSegments (PatternSegmentNonWF.doubleStar :: ps) xs
  | p :: ps, x :: xs =>
      p.matchS x && matchSegments ps xs

def getFilesAndDirs (dir : String) : IO (Array String) := do
  let files ← findRec dir (fun _ => true)
  let dirs ← findDirsRec dir
  let mut arr := #[]
  for p in files do
    arr := arr.push (stripDotSlash p.toString)
  for p in dirs do
    arr := arr.push (stripDotSlash p.toString)
  return arr

def globFS (pattern : NonEmptyList PatternSegmentNonWF) : IO (Array String) := do
  let all ← getFilesAndDirs "."
  let mut matched := #[]
  for p in all do
    let pathSegments := (p.splitOn "/").filter (· ≠ "")
    if matchSegments pattern.toList pathSegments then
      matched := matched.push p
  return matched

def globWithDirMark (patternStr : String) : IO (Array String) := do
  let pat ← match PatternValidated.patternStrict? patternStr with
    | .ok p => match NonEmptyList.fromList? p.pattern with
      | some nel => pure nel
      | none => throw (IO.userError "Empty pattern")
    | .error e => throw (IO.userError s!"Invalid pattern: {e}")

  let files ← findRec "." (fun _ => true)
  let dirs ← findDirsRec "."

  let mut allItems := #[]
  for p in files do
    allItems := allItems.push (stripDotSlash p.toString, false)
  for p in dirs do
    allItems := allItems.push (stripDotSlash p.toString, true)

  let mut matched := #[]
  for (p, isDir) in allItems do
    let pathSegments := (p.splitOn "/").filter (· ≠ "")
    if matchSegments pat.toList pathSegments then
      if isDir then
        matched := matched.push (p ++ "/")
      else
        matched := matched.push p
  return matched.qsort (· < ·)

def assertAreEqualAndReturnFirst (a : PatternValidated) (b : List PatternSegmentNonWF) : PatternValidated :=
  if a.pattern == b then a
  else panic! s!"assertAreEqualAndReturnFirst failed: {repr a} != {repr b}"

def assertGlob (pattern : PatternValidated) (expected : Array String) : IO Unit := do
  match NonEmptyList.fromList? pattern.pattern with
  | some nel =>
    let actual ← globFS nel
    assertEq s!"assertGlob {nel}" expected actual
  | none => throw (IO.userError "Pattern cannot be empty")

def assertGlobMany (patterns : NonEmptyList (NonEmptyList PatternSegmentNonWF)) (expected : Array String) : IO Unit := do
  let mut actual := #[]
  for p in patterns.toList do
    let res ← globFS p
    for r in res do
      if !actual.contains r then
        actual := actual.push r
  assertEq s!"assertGlobMany" expected actual

end
