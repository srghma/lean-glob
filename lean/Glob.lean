import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.NonEmptyString
import Glob.NonEmptyList
import Glob.NEFromTo

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

--------------------------
inductive PatternSegmentNonWF where
  | doubleStar : PatternSegmentNonWF
  | oneStar : PatternSegmentNonWF
  | lit : NonEmptyString -> PatternSegmentNonWF
  deriving Inhabited, Repr, BEq, Ord, Hashable, DecidableEq

def PatternSegmentNonWF.toString : PatternSegmentNonWF → String
| .doubleStar => "**"
| .oneStar => "*"
| .lit s => NonEmptyString.toString s

def PatternSegmentNonWF.fromNES (nes : NonEmptyString) : PatternSegmentNonWF :=
  match nes.val with
  | "**" => .doubleStar
  | "*"  => .oneStar
  | _    => .lit nes

open Lean Meta

set_option diagnostics true

instance : ToExpr PatternSegmentNonWF where
  toTypeExpr := mkConst ``PatternSegmentNonWF
  toExpr
  | .doubleStar => mkConst ``PatternSegmentNonWF.doubleStar
  | .oneStar    => mkConst ``PatternSegmentNonWF.oneStar
  | .lit s      => mkApp (mkConst ``PatternSegmentNonWF.lit) (toExpr s)

abbrev PatternNonWF' := List PatternSegmentNonWF
abbrev PatternNonWF := NonEmptyList PatternSegmentNonWF

def PatternNonWF'.toString (ps : PatternNonWF') : String := String.intercalate "/" (ps.map PatternSegmentNonWF.toString)
def PatternNonWF'.fromStringStrict (s : String) : Option PatternNonWF' := (ToNE.Traverse.«LS->LNES» (s.split (· == '/'))).map (·.map PatternSegmentNonWF.fromNES)

def PatternNonWF'.fromStringLax (s : String) : PatternNonWF' := (ToNE.FilterMap.«LS->LNES» (s.split (· == '/'))).map (PatternSegmentNonWF.fromNES)


def PatternNonWF.toString (ps : PatternNonWF) : String := PatternNonWF'.toString ps.toList
def PatternNonWF.fromStringStrict (s : String) : Option PatternNonWF := PatternNonWF'.fromStringStrict s >>= NonEmptyList.fromList?

set_option diagnostics.threshold 50

elab "patternNonWFLax" pat:str : term => do
  let s := pat.getString
  return (Lean.toExpr (PatternNonWF'.fromStringLax s))

elab "patternNonWFStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF.fromStringStrict s with
  | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
  | none   => throwError s!"invalid non-well-formed pattern: {s}"

#guard nel![PatternSegmentNonWF.oneStar] = nel![PatternSegmentNonWF.oneStar]
#guard PatternNonWF.fromStringStrict "*" = .some nel![PatternSegmentNonWF.oneStar]
#guard patternNonWFLax "*" = [PatternSegmentNonWF.oneStar]
#guard patternNonWFStrict "*" = nel![PatternSegmentNonWF.oneStar]

-------------

inductive OneStarOrLit where
  | oneStar : OneStarOrLit
  | lit : NonEmptyString -> OneStarOrLit
  deriving Inhabited, Repr, BEq, Ord, Hashable, DecidableEq

inductive DoubleStarOnStartOrEnd where
  | none : DoubleStarOnStartOrEnd -- pattern was like `anything/file.txt`
  | onStart : DoubleStarOnStartOrEnd -- pattern was like `**/anything/file.txt`
  | onEnd : DoubleStarOnStartOrEnd -- pattern was like `anything/**/file.txt`
  | onStartAndEnd : DoubleStarOnStartOrEnd -- pattern was like `**/anything/**/file.txt`
  deriving Inhabited, Repr, BEq, Ord, Hashable, DecidableEq

structure Pattern where
  doubleStarOnStartOrEnd : DoubleStarOnStartOrEnd
  dirs : List (NonEmptyList OneStarOrLit)
  file : OneStarOrLit
  deriving Inhabited, Repr, BEq, Ord, Hashable, DecidableEq

instance : ToExpr OneStarOrLit where
  toTypeExpr := mkConst `OneStarOrLit
  toExpr
    | .oneStar => mkConst `OneStarOrLit.oneStar
    | .lit s   => mkApp (mkConst `OneStarOrLit.lit) (toExpr s)

instance : ToExpr DoubleStarOnStartOrEnd where
  toTypeExpr := mkConst `DoubleStarOnStartOrEnd
  toExpr
    | .none          => mkConst `DoubleStarOnStartOrEnd.none
    | .onStart       => mkConst `DoubleStarOnStartOrEnd.onStart
    | .onEnd         => mkConst `DoubleStarOnStartOrEnd.onEnd
    | .onStartAndEnd => mkConst `DoubleStarOnStartOrEnd.onStartAndEnd

instance : ToExpr Pattern where
  toTypeExpr := mkConst `Pattern
  toExpr p := mkApp3 (mkConst `Pattern.mk) (toExpr p.doubleStarOnStartOrEnd) (toExpr p.dirs) (toExpr p.file)

-------------------- To String

def OneStarOrLit.toPatternSegmentNonWF : OneStarOrLit → PatternSegmentNonWF
  | .oneStar => .oneStar
  | .lit s => .lit s

def DoubleStarOnStartOrEnd.prefix : DoubleStarOnStartOrEnd → Bool
  | .onStart => true
  | .onStartAndEnd => true
  | _ => false

def DoubleStarOnStartOrEnd.suffix : DoubleStarOnStartOrEnd → Bool
  | .onEnd => true
  | .onStartAndEnd => true
  | _ => false

def Pattern.toPatternNonWF' (p : Pattern) : PatternNonWF' :=
  let _prefix := if p.doubleStarOnStartOrEnd.prefix then [.doubleStar] else []
  let dirStrs := p.dirs.flatMap (fun group => group.toList.map OneStarOrLit.toPatternSegmentNonWF)
  let suffix := if p.doubleStarOnStartOrEnd.suffix then [.doubleStar] else []
  let fileStr := OneStarOrLit.toPatternSegmentNonWF p.file
  let parts := _prefix ++ dirStrs ++ suffix ++ [fileStr]
  parts

def Pattern.toString (p : Pattern) : String := PatternNonWF'.toString (Pattern.toPatternNonWF' p)

#guard Pattern.toString (Pattern.mk .none [] .oneStar) = "*"

------------------------------

def Pattern.fromPatternNonWF (ps : List PatternSegmentNonWF) : Pattern :=
  let rec go
    (segments : List PatternSegmentNonWF)
    (accDirs : List (NonEmptyList OneStarOrLit))
    (cur : List OneStarOrLit)
    (sawDoubleStarAtStart : Bool)
    (sawDoubleStarAtEnd : Bool)
    : Pattern :=
    match segments with
    | [] =>
      match cur.reverse with
      | [] =>
        { doubleStarOnStartOrEnd :=
            if sawDoubleStarAtStart && sawDoubleStarAtEnd then .onStartAndEnd
            else if sawDoubleStarAtStart then .onStart
            else if sawDoubleStarAtEnd then .onEnd
            else .none
        , dirs := accDirs.reverse
        , file := .oneStar  -- fallback
        }
      | fileSeg :: revDirSegs =>
        let file := fileSeg
        let maybeGroup := NonEmptyList.fromList? revDirSegs.reverse
        let allDirs := maybeGroup.map (fun g => g :: accDirs) |> Option.getD accDirs
        { doubleStarOnStartOrEnd :=
            if sawDoubleStarAtStart && sawDoubleStarAtEnd then .onStartAndEnd
            else if sawDoubleStarAtStart then .onStart
            else if sawDoubleStarAtEnd then .onEnd
            else .none
        , dirs := (allDirs.getD []).reverse
        , file := file
        }

    | .doubleStar :: rest =>
      let sawStart := accDirs == [] && cur == []
      let sawEnd := rest.isEmpty
      let sawDoubleStarAtStart := sawDoubleStarAtStart || sawStart
      let sawDoubleStarAtEnd := sawDoubleStarAtEnd || sawEnd
      match NonEmptyList.fromList? cur.reverse with
      | some group => go rest (group :: accDirs) [] sawDoubleStarAtStart sawDoubleStarAtEnd
      | none => go rest accDirs [] sawDoubleStarAtStart sawDoubleStarAtEnd

    | .oneStar :: rest =>
      go rest accDirs (OneStarOrLit.oneStar :: cur) sawDoubleStarAtStart sawDoubleStarAtEnd

    | .lit s :: rest =>
      go rest accDirs (OneStarOrLit.lit s :: cur) sawDoubleStarAtStart sawDoubleStarAtEnd

  go ps [] [] false false

elab "patternLax" pat:str : term => do
  let s := pat.getString
  return (Lean.toExpr (Pattern.fromPatternNonWF $ PatternNonWF'.fromStringLax s))

elab "patternStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF.fromStringStrict s with
  | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
  | none   => throwError s!"invalid non-well-formed pattern: {s}"

#guard Pattern.fromPatternNonWF [] = Pattern.mk .none [] .oneStar
#guard Pattern.fromPatternNonWF (patternNonWFLax"") = Pattern.mk .none [] .oneStar

-- | Input Pattern                | Segments Parsed                         | Output Pattern                                               |
-- | ---------------------------- | --------------------------------------- | ------------------------------------------------------------ |
-- | `""`                         | `[]`                                    | `none × [] × *` (just return match all files in current dir) |
-- | `"**"`                       | `[**]`                                  | `onStart × [] × *` (default fallback for file?)              | -- curr onStartAndEnd
-- | `"*"`                        | `[*]`                                   | `none × [] × *`                                              |
-- | `"**/*"`                     | `[**, *]`                               | `onStart × [] × *`                                           |
-- | `"**/**"`                    | `[**, **]`                              | `onStart × [] × *`                                           | -- curr onStartAndEnd
-- | `"**/foo.txt"`               | `[**, "foo.txt"]`                       | `onStart × [] × "foo.txt"`                                   |
-- | `"*/foo.txt"`                | `[*,"foo.txt"]`                         | `none × [[*]] × "foo.txt"`                                   |
-- | `"*/*/foo.txt"`              | `[* , *, "foo.txt"]`                    | `none × [[*,*]] × "foo.txt"`                                 |
-- | `"*/*/**/*/*/foo.txt"`       | `[* , *, **, *, *, "foo.txt"]`          | `none × [[*,*], [*,*]] × "foo.txt"`                          |
-- | `"**/*/*"`                   | `[**, *, *]`                            | `onStart × [[*]] × *`                                        |
-- | `"foo/bar.txt"`              | `["foo", "bar.txt"]`                    | `none × [["foo"]] × "bar.txt"`                               |
-- | `"**/foo/*/bar.txt"`         | `[**, "foo", *, "bar.txt"]`             | `onStart × [["foo", *]] × "bar.txt"`                         |
-- | `"**/foo/**/bar.txt"`        | `[**, "foo", **, "bar.txt"]`            | `onStartAndEnd × [["foo"]] × "bar.txt"`                      |
-- | `"**/foo/**/**/bar.txt"`     | `[**, "foo", **, **, "bar.txt"]`        | `onStartAndEnd × [["foo"]] × "bar.txt"`                      |
-- | `"**/foo/**/baz/**/bar.txt"` | `[**, "foo", **, "baz", **, "bar.txt"]` | `onStartAndEnd × [["foo"], ["baz"]] × "bar.txt"`             |

#guard patternLax "" = Pattern.mk .none [] .oneStar
#guard patternLax "**" = Pattern.mk .onStartAndEnd [] .oneStar
#guard patternLax "*" = Pattern.mk .none [] .oneStar
#guard patternLax "**/*" = Pattern.mk .onStart [] .oneStar
#guard patternLax "**/**" = Pattern.mk .onStartAndEnd [] .oneStar
#guard patternLax "**/foo.txt" = Pattern.mk .onStart [] (.lit (nes! "foo.txt"))
#guard patternLax "*/foo.txt" = Pattern.mk .none [] .oneStar -- [nel![.oneStar]] (.lit (nes! "foo.txt"))
/- #guard patternLax "*/*/foo.txt" = Pattern.mk .none [nel![.oneStar, .oneStar]] (.lit (nes! "foo.txt")) -/
/- #guard patternLax "*/*/**/*/*/foo.txt" = Pattern.mk .none [nel![.oneStar, .oneStar], nel![.oneStar, .oneStar]] (.lit (nes! "foo.txt")) -/
/- #guard patternLax "**/*/*" = Pattern.mk .onStart [nel![.oneStar]] .oneStar -/
/- #guard patternLax "foo/bar.txt" = Pattern.mk .none [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/*/bar.txt" = Pattern.mk .onStart [nel![.lit (nes! "foo"), .oneStar]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/**/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/**/baz/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")], nel![.lit (nes! "baz")]] (.lit (nes! "bar.txt")) -/

def FilePath.componentsNES (p : FilePath) : List NonEmptyString :=
  ToNE.FilterMap.«LS->LNES» p.components

-- Test cases from the table:

-- | Input Pattern                | Segments Parsed                         | Output Pattern                                               |
-- | `""`                         | `[]`                                    | `none × [] × *` (just return match all files in current dir) |

-- -- | `"**"`                       | `[**]`                                  | `onStart × [] × *` (default fallback for file?)              |
-- #guard Pattern.fromPatternNonWF [.doubleStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .oneStar }

-- -- | `"*"`                        | `[*]`                                   | `none × [] × *`                                              |
-- #guard Pattern.fromPatternNonWF [.oneStar] =
--   { doubleStarOnStartOrEnd := .none, dirs := [], file := .oneStar }

-- -- | `"**/*"`                     | `[**, *]`                               | `onStart × [] × *`                                           |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .oneStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .oneStar }

-- -- | `"**/**"`                    | `[**, **]`                              | `onStart × [] × *`                                           |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .doubleStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .oneStar }

-- -- | `"**/foo.txt"`               | `[**, "foo.txt"]`                       | `onStart × [] × "foo.txt"`                                   |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .lit (nes "foo.txt") }

-- -- | `"*/foo.txt"`                | `[*,"foo.txt"]`                         | `none × [[*]] × "foo.txt"`                                   |
-- #guard Pattern.fromPatternNonWF [.oneStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.oneStar]], file := .lit (nes "foo.txt") }

-- -- | `"*/*/foo.txt"`              | `[* , *, "foo.txt"]`                    | `none × [[*,*]] × "foo.txt"`                                 |
-- #guard Pattern.fromPatternNonWF [.oneStar, .oneStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.oneStar, .oneStar]], file := .lit (nes "foo.txt") }

-- -- | `"*/*/**/*/*/foo.txt"`       | `[* , *, **, *, *, "foo.txt"]`          | `none × [[*,*], [*,*]] × "foo.txt"`                          |
-- #guard Pattern.fromPatternNonWF [.oneStar, .oneStar, .doubleStar, .oneStar, .oneStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.oneStar, .oneStar], nel![.oneStar, .oneStar]], file := .lit (nes "foo.txt") }

-- -- | `"**/*/*"`                   | `[**, *, *]`                            | `onStart × [[*]] × *`                                        |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .oneStar, .oneStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [nel![.oneStar]], file := .oneStar }

-- -- | `"foo/bar.txt"`              | `["foo", "bar.txt"]`                    | `none × [["foo"]] × "bar.txt"`                               |
-- #guard Pattern.fromPatternNonWF [.lit (nes "foo"), .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.lit (nes "foo")]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/*/bar.txt"`         | `[**, "foo", *, "bar.txt"]`             | `onStart × [["foo", *]] × "bar.txt"`                         |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .oneStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [nel![.lit (nes "foo"), .oneStar]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/**/bar.txt"`        | `[**, "foo", **, "bar.txt"]`            | `onStartAndEnd × [["foo"]] × "bar.txt"`                      |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .doubleStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStartAndEnd, dirs := [nel![.lit (nes "foo")]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/**/**/bar.txt"`     | `[**, "foo", **, **, "bar.txt"]`        | `onStartAndEnd × [["foo"]] × "bar.txt"`                      |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .doubleStar, .doubleStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStartAndEnd, dirs := [nel![.lit (nes "foo")]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/**/baz/**/bar.txt"` | `[**, "foo", **, "baz", **, "bar.txt"]` | `onStartAndEnd × [["foo"], ["baz"]] × "bar.txt"`             |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .doubleStar, .lit (nes "baz"), .doubleStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStartAndEnd, dirs := [nel![.lit (nes "foo")], nel![.lit (nes "baz")]], file := .lit (nes "bar.txt") }



-- partial def walkDir
--   (p : FilePath)
--   (enter : String → Bool)
--   (shouldAddFileToListOfFilepaths : String → Bool) : IO (Array FilePath) :=
--   go p
-- where
--   go (p : FilePath) : IO (Array FilePath) := do
--     if !enter p.fileName then
--       return #[]

--     let entries ← p.readDir
--     let results ← entries.mapM fun d => do
--       let root := d.root
--       let fileName := d.fileName
--       let path := d.path
--       let includeSelf := if shouldAddFileToListOfFilepaths fileName then #[path] else #[]

--       match (← path.metadata.toBaseIO) with
--       | .ok { type := .symlink, .. } =>
--         let real ← IO.FS.realPath path
--         if (← real.isDir) then
--           -- don't call enter on symlink again
--           if enter p.fileName then
--             let sub ← go real
--             return includeSelf ++ sub
--           else
--             return includeSelf
--         else
--           return includeSelf
--       | .ok { type := .dir, .. } =>
--         let sub ← go path
--         return includeSelf ++ sub
--       | .ok =>
--         return includeSelf
--       | .error (.noFileOrDirectory ..) =>
--         return #[]
--       | .error e =>
--         throw e

--     return results.join
