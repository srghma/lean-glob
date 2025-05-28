import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.Utils.NonEmptyString
import Glob.Utils.NonEmptyList
import Glob.Utils.NEFromTo
-- import Mathlib.Data.List.Induction
-- import Aesop
-- import LeanCopilot
import Glob.NonWF


open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def normalizeSegmentsGo (acc : List PatternSegmentNonWF) (remaining : List PatternSegmentNonWF) : List PatternSegmentNonWF :=
  match remaining with
  | [] => acc
  | [x] => (x :: acc)
  | .doubleStar :: .doubleStar :: rest => normalizeSegmentsGo acc (.doubleStar :: rest)
  | .doubleStar :: .oneStar :: rest => normalizeSegmentsGo (.oneStar :: acc) (.doubleStar :: rest)
  | x :: rest => normalizeSegmentsGo (x :: acc) rest

def normalizeSegments (ps : List PatternSegmentNonWF) : List PatternSegmentNonWF := (normalizeSegmentsGo [] ps).reverse

#guard normalizeSegments (patternNonWFLax "") == (patternNonWFLax "")
#guard normalizeSegments (patternNonWFLax "**") == (patternNonWFLax "**")
#guard normalizeSegments (patternNonWFLax "*") == (patternNonWFLax "*")
#guard normalizeSegments (patternNonWFLax "**/*") == (patternNonWFLax "*/**")
#guard normalizeSegments (patternNonWFLax "**/**") == (patternNonWFLax "**")
#guard normalizeSegments (patternNonWFLax "**/foo.txt") == (patternNonWFLax "**/foo.txt")
#guard normalizeSegments (patternNonWFLax "*/foo.txt") == (patternNonWFLax "*/foo.txt")
#guard normalizeSegments (patternNonWFLax "*/*/foo.txt") == (patternNonWFLax "*/*/foo.txt")
#guard normalizeSegments (patternNonWFLax "*/*/**/*/*/foo.txt") == (patternNonWFLax "*/*/*/*/**/foo.txt")
#guard normalizeSegments (patternNonWFLax "**/*/*") == (patternNonWFLax "*/*/**")
#guard normalizeSegments (patternNonWFLax "foo/bar.txt") == (patternNonWFLax "foo/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/*/bar.txt") == (patternNonWFLax "**/foo/*/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/**/bar.txt") == (patternNonWFLax "**/foo/**/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/**/**/bar.txt") == (patternNonWFLax "**/foo/**/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/**/baz/**/bar.txt") == (patternNonWFLax "**/foo/**/baz/**/bar.txt")
#guard normalizeSegments (patternNonWFLax "*/**/*/foo/*/**/*/baz/*/**/*/bar.txt") == (patternNonWFLax "*/*/**/foo/*/*/**/baz/*/*/**/bar.txt")
