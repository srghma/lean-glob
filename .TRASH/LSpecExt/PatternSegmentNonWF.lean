module
public import LSpec
public import Glob.NonWF.Normalize
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
public import LSpecExt.NonEmptyString

@[expose] public section

open NonEmpty.String NonEmpty.List
open LSpec SlimCheck Gen

def genPatternSegmentNonWF : Gen PatternSegmentNonWF := do
  let i ← Gen.choose Nat 0 2
  match i with
  | 0 => return PatternSegmentNonWF.doubleStar
  | 1 => return PatternSegmentNonWF.oneStar
  | _ => do
    let lit ← Gen.elements #["foo", "bar", "baz"]
    if h : lit ≠ "" then
      return PatternSegmentNonWF.lit ⟨lit, h⟩
    else
      return PatternSegmentNonWF.lit ⟨"x", by decide⟩

def PatternSegmentNonWF.shrink (x : PatternSegmentNonWF) : List PatternSegmentNonWF :=
  match x with
  | .lit s => (NonEmptyString.shrinkByRemovingSuffixes s).map .lit
  | .oneStar => []
  | .doubleStar => []
  | .regex _ => []

end
