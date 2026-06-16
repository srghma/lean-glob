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
-- import Mathlib.Data.List.Induction
-- import Aesop
-- import LeanCopilot
public import Glob.NonWF.Types
public import Glob.WF.Types
public import Glob.WF.Elab

@[expose] public section

open NonEmpty.String NonEmpty.List
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

-- partial def walkDir
--   (p : FilePath)
--   (enter : String → Bool)
--   (shouldAddFileToListOfFilepaths : String → Bool) : IO (Array FilePath) :=
--   go p
-- where
--   go (p : FilePath) : IO (Array FilePath) := do
--     if !enter p.fileName then
--       return #[]
--
--     let entries ← p.readDir
--     let results ← entries.mapM fun d => do
--       let root := d.root
--       let fileName := d.fileName
--       let path := d.path
--       let includeSelf := if shouldAddFileToListOfFilepaths fileName then #[path] else #[]
--
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
--       | .ok => return includeSelf
--       | .error (.noFileOrDirectory ..) => return #[]
--       | .error e => throw e
--     return results.join
end
