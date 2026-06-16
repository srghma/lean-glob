module
public meta import Glob.NonWF.Types
public import NonEmpty.String.ToExpr
public import NonEmpty.List.ToExpr

open Lean Meta Elab NonEmpty.String NonEmpty.List

elab "patternNonWFLax" pat:str : term => return Lean.toExpr (PatternNonWF'.fromStringLax pat.getString)

elab "patternNonWFStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF.fromStringStrict s with
  | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
  | none => throwError s!"invalid non-well-formed pattern: {s}"

#guard NonEmptyList.mk [PatternSegmentNonWF.oneStar] (by simp) = NonEmptyList.mk [PatternSegmentNonWF.oneStar] (by simp)
#guard PatternNonWF.fromStringStrict "*" = .some (NonEmptyList.mk [PatternSegmentNonWF.oneStar] (by simp))
#guard patternNonWFLax "*" = [PatternSegmentNonWF.oneStar]
#guard patternNonWFStrict "*" = NonEmptyList.mk [PatternSegmentNonWF.oneStar] (by simp)
