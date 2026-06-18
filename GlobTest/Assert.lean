module
public import Init.System.IO

@[expose] public section

open System (FilePath)
open IO.FS

namespace GlobTest.Spec.Assert

/-- Assert two values are equal, throwing a descriptive error otherwise. -/
def assertEq [BEq α] [Repr α] (label : String) (expected actual : α) : IO Unit := do
  unless expected == actual do
    throw <| IO.userError s!"{label}: expected {reprStr expected}, got {reprStr actual}"

def assertBool (label : String) (expected actual : Bool) : IO Unit :=
  assertEq label expected actual

def assertIsEmpty [Repr α] (label : String) (xs : Array α) : IO Unit := do
  unless xs.isEmpty do
    throw <| IO.userError s!"{label}: expected empty, got {reprStr xs}"

def assertIsNotEmpty [Repr α] (label : String) (xs : Array α) : IO Unit := do
  when xs.isEmpty do
    throw <| IO.userError s!"{label}: expected non-empty, got empty"

/-- Run `act` inside a fresh temporary directory, restoring the previous working
directory afterwards. Each parallel test gets its own isolated dir. -/
def withinTempDir (act : IO α) : IO α := do
  let prev ← IO.currentDir
  -- unique-ish directory name based on a high-resolution timestamp.
  let stamp ← IO.monoNanosNow
  let dir : FilePath := prev / s!".spec-tmp-{stamp}"
  IO.FS.createDirAll dir
  IO.setCurrentDir dir
  try
    act
  finally
    IO.setCurrentDir prev
    try IO.FS.removeDirAll dir catch _ => pure ()

end GlobTest.Spec.Assert
