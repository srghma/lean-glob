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
public import Glob.WF.IO
public import Tree
public import Spec.Assert
public import Spec.Core

open System (FilePath)
open NonEmpty.List
open Spec.Assert

@[expose] public section

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

def assertAreEqualAndReturnFirst (a : PatternValidated) (b : List PatternSegmentNonWF) : PatternValidated :=
  if a.pattern == b then a
  else panic! s!"assertAreEqualAndReturnFirst failed: {repr a} != {repr b}"
