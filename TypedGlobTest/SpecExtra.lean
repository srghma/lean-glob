module
public import Init.System.IO
public import Init.System.FilePath
public import Spec.Core
public import Spec.Assert
public import TypedGlob.IO
public import Tree
public import Glob.NonWF.Types

@[expose] public section

open System (FilePath)
open IO.FS
open NonEmpty.List
open NonEmpty.String
open Spec.Core
open Spec.Assert

def assertAreEqualAndReturnFirst (a : PatternValidated) (b : List PatternSegmentNonWF) : PatternValidated :=
  if a.pattern == b then a
  else panic! s!"assertAreEqualAndReturnFirst failed: {repr a} != {repr b}"

def assertTypedGlob (tmpDir : FilePath) (pattern : PatternValidated) (expected : Array String) : IO Unit := do
  match NonEmptyList.fromList? pattern.pattern with
  | some nel =>
    let tmpPosixDir := Posix.IO.wrapAbs! .Dir ⟨tmpDir.toString ++ "/"⟩
    let actual ← typedGlobFS tmpPosixDir pattern
    let actualStrs := actual.map fun
      | .inl f => toString f
      | .inr d => toString d
    assertEq s!"assertTypedGlob {nel}" expected actualStrs
  | none => throw (IO.userError "Pattern cannot be empty")
