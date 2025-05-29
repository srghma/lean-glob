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
import Glob.WF.Types
import Glob.WF.Elab

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

-- elab "patternStrict" pat:str : term => do
--   let s := pat.getString
--   match PatternNonWF.fromStringStrict s with
--   | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
--   | none   => throwError s!"invalid non-well-formed pattern: {s}"
--
-- #guard Pattern.fromPatternNonWF [] = Pattern.mk .none [] .oneStar
-- #guard Pattern.fromPatternNonWF (patternNonWFLax"") = Pattern.mk .none [] .oneStar
--
-- #guard patternLax "" = Pattern.mk .none [] .oneStar
-- #guard patternLax "**" = Pattern.mk .onStartAndEnd [] .oneStar
-- #guard patternLax "*" = Pattern.mk .none [] .oneStar
-- #guard patternLax "**/*" = Pattern.mk .onStart [] .oneStar
-- #guard patternLax "**/**" = Pattern.mk .onStartAndEnd [] .oneStar
-- #guard patternLax "**/foo.txt" = Pattern.mk .onStart [] (.lit (nes! "foo.txt"))
-- #guard patternLax "*/foo.txt" = Pattern.mk .none [] .oneStar -- [nel![.oneStar]] (.lit (nes! "foo.txt"))
-- #guard patternLax "*/*/foo.txt" = Pattern.mk .none [nel![.oneStar, .oneStar]] (.lit (nes! "foo.txt"))
-- #guard patternLax "*/*/**/*/*/foo.txt" = Pattern.mk .none [nel![.oneStar, .oneStar], nel![.oneStar, .oneStar]] (.lit (nes! "foo.txt"))
-- #guard patternLax "**/*/*" = Pattern.mk .onStart [nel![.oneStar]] .oneStar
-- #guard patternLax "foo/bar.txt" = Pattern.mk .none [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt"))
-- #guard patternLax "**/foo/*/bar.txt" = Pattern.mk .onStart [nel![.lit (nes! "foo"), .oneStar]] (.lit (nes! "bar.txt"))
-- #guard patternLax "**/foo/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt"))
-- #guard patternLax "**/foo/**/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt"))
-- #guard patternLax "**/foo/**/baz/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")], nel![.lit (nes! "baz")]] (.lit (nes! "bar.txt"))



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
