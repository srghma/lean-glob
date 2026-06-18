module
public meta import Glob.NonWF.Types
public import NonEmpty.String.ToExpr
public import NonEmpty.List.ToExpr

open Lean Meta Elab NonEmpty.String NonEmpty.List

elab "patternNonWFLax" pat:str : term => return Lean.toExpr (PatternNonWF'.fromStringLax pat.getString)

elab "patternNonWFStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF.fromStringStrict s with
  | .ok (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
  | .error .emptySegment => throwError s!"invalid non-well-formed pattern: {s}"
  | .error (.invalidRegex _) => throwError s!"invalid regex in pattern: {s}"

#guard ![PatternSegmentNonWF.oneStar] = ![PatternSegmentNonWF.oneStar]
#guard (PatternNonWF.fromStringStrict "*").toOption = some (![PatternSegmentNonWF.oneStar])
#guard patternNonWFLax "*" = [PatternSegmentNonWF.oneStar]
#guard patternNonWFStrict "*" = ![PatternSegmentNonWF.oneStar]
