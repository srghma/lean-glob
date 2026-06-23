module
public import Init.System.IO
public import Lean
public import Lean.Data.RBMap
public import Std.Data.HashSet
public import Lean.Data.RBTree
public import Lean.Elab.Term
public import Init.Meta
public import Lean.Parser.Term
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
public import Glob.NonWF.Types
public import Glob.NonWF.Normalize
public meta import Glob.NonWF.Macros
public meta import Glob.WF.Types

@[expose] public section

open NonEmpty.String NonEmpty.List

elab "patternLax" pat:str : term => do
  let s := pat.getString
  match (PatternValidated.mk? $ normalizeSegments $ PatternNonWF'.fromStringLax s) with
  | .error e => throwError e.toHumanReadable
  | .ok pat => return (Lean.toExpr pat)

-- TODO: patternStrict -> glob (can have option `normalize` which means it will be lax). patternNonWF -> glob_impl
-- TODO: normalization always gives valid?
elab "patternStrict" pat:str : term => do
  match PatternValidated.patternStrict? pat.getString with
  | .error e => throwError e
  | .ok pat => return (Lean.toExpr pat)
-- TODO: parse to `inductive ... where | glob GlobVal | envVar; struct ... where startsWithHome : Bool; components : List ...`

elab "patternStrictWithEnvVars" pat:str : term => do
  match PatternValidated.patternStrictWithEnvVars? pat.getString with
  | .error e => throwError e
  | .ok _ =>
    let stx ← `(PatternValidated.patternStrictWithEnvVars_unchecked $pat)
    Lean.Elab.Term.elabTerm stx none

/--
info: Pattern cannot be empty.
-/
#guard_msgs in #check_failure patternLax ""
#guard (patternLax "**" |>.pattern) == patternNonWFLax "**"
#guard (patternLax "*" |>.pattern) == patternNonWFLax "*"
#guard (patternLax "**/*" |>.pattern) == patternNonWFLax "*/**"
#guard (patternLax "**/**" |>.pattern) == patternNonWFLax "**"
#guard (patternLax "**/foo.txt" |>.pattern) == patternNonWFLax "**/foo.txt"
#guard (patternLax "*/foo.txt" |>.pattern) == patternNonWFLax "*/foo.txt"
#guard (patternLax "*/*/foo.txt" |>.pattern) == patternNonWFLax "*/*/foo.txt"
#guard (patternLax "*/*/**/*/*/foo.txt" |>.pattern) == patternNonWFLax "*/*/*/*/**/foo.txt"
#guard (patternLax "**/*/*" |>.pattern) == patternNonWFLax "*/*/**"
#guard (patternLax "foo/bar.txt" |>.pattern) == patternNonWFLax "foo/bar.txt"
#guard (patternLax "**/foo/*/bar.txt" |>.pattern) == patternNonWFLax "**/foo/*/bar.txt"
#guard (patternLax "**/foo/**/bar.txt" |>.pattern) == patternNonWFLax "**/foo/**/bar.txt"
#guard (patternLax "**/foo/**/**/bar.txt" |>.pattern) == patternNonWFLax "**/foo/**/bar.txt"
#guard (patternLax "**/foo/**/baz/**/bar.txt" |>.pattern) == patternNonWFLax "**/foo/**/baz/**/bar.txt"
#guard (patternLax "*/**/*/foo/*/**/*/baz/*/**/*/bar.txt" |>.pattern) == patternNonWFLax "*/*/**/foo/*/*/**/baz/*/*/**/bar.txt"

/--
info: Pattern cannot be empty.
-/
#guard_msgs in #check_failure (patternStrict "")
/--
info: { pattern := [PatternSegmentNonWF.lit { toString := "s", isNonEmpty := ⋯ }], valid_sequence := ⋯ } : PatternValidated
-/
#guard_msgs in #check (patternStrict "s")
/--
info: Probably You wanted to write */*/**/foo/*/*/**/baz/*/*/**/bar.txt
Pattern doesn't follow rules:
  1. Double stars can follow only * or "foo" (**/** is disallowed).
  2. One stars can follow only * or "foo" (**/* is disallowed).
-/
#guard_msgs in #check_failure (patternStrict "*/**/*/foo/*/**/*/baz/*/**/*/bar.txt")
end
