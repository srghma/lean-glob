import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.Data.NonEmptyString
import Glob.Data.NonEmptyList
import Glob.Utils.NEFromTo
-- import Mathlib.Data.List.Induction
-- import Aesop
-- import LeanCopilot
import Glob.NonWF.Types
import Glob.NonWF.Normalize
import Glob.WF.Types

elab "patternLax" pat:str : term => do
  let s := pat.getString
  match (PatternValidated.mk? $ normalizeSegments $ PatternNonWF'.fromStringLax s) with
  | .error e => throwError e.toHumanReadable
  | .ok pat => return (Lean.toExpr pat)

-- (normalize:Bool = false)
elab "patternStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF'.fromStringStrict s with
  | .none => throwError "did some segment was empty? e.g. `foo//bar` should be `foo/bar`"
  | .some pat => match (PatternValidated.mk? pat) with
    | .error .invalidEmpty => throwError PatternValidatedError.invalidEmpty.toHumanReadable
    | .error .invalidWrongOrdering => throwError (s!"Probably You wanted to write {PatternNonWF'.toString $ normalizeSegments pat}\n{PatternValidatedError.invalidWrongOrdering.toHumanReadable}")
    | .ok pat => return (Lean.toExpr pat)

#check_failure patternLax ""
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

#check_failure (patternStrict "")
#check (patternStrict "s")
#check_failure (patternStrict "*/**/*/foo/*/**/*/baz/*/**/*/bar.txt")
