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
public import Glob.NonWF.Macros

@[expose] public section

open NonEmpty.String NonEmpty.List
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

-- TODO DList? idris2 SnocList? to prove easier?
-- theorem normalizeSegments_id (xs : List PatternSegmentNonWF) :
--   isValidSequence xs → normalizeSegments xs = xs

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
end
