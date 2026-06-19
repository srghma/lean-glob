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
public import Glob.WF.Types
public import Glob.WF.Elab

@[expose] public section

open NonEmpty.String NonEmpty.List
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def stripDirPrefix (dir : String) (path : String) : Substring.Raw :=
  let dirWithSlash := if dir.endsWith "/" then dir else dir ++ "/"
  if path.startsWith dirWithSlash then
    path.toRawSubstring.drop dirWithSlash.length
  else
    path.toRawSubstring

partial def matchSegments (pattern : List PatternSegmentNonWF) (path : List Substring.Raw) : Bool :=
  match pattern, path with
  | [], [] => true
  | [], _ => false
  | PatternSegmentNonWF.doubleStar :: ps, [] => matchSegments ps []
  | _ :: _, [] => false
  | PatternSegmentNonWF.doubleStar :: ps, x :: xs =>
      matchSegments ps (x :: xs) || matchSegments (PatternSegmentNonWF.doubleStar :: ps) xs
  | p :: ps, x :: xs =>
      p.matchRawSub x && matchSegments ps xs

structure DirWalker where
  root : System.FilePath
  prune : System.FilePath → IO Bool := fun _ => pure false

partial def DirWalker.forInRec {β : Type} (w : DirWalker) (current : System.FilePath) (init : β) (f : (System.FilePath × Metadata) → β → IO (ForInStep β)) : IO (ForInStep β) := do
  try
    let entries ← current.readDir
    let mut state := init
    for entry in entries do
      let path := entry.path
      let md ← path.metadata
      let isDir := md.type == FileType.dir

      -- If the user wants to prune this directory BEFORE visiting it, we can do it here.
      -- But standard `os.walk` visits the directory, THEN you prune.
      -- Let's just visit it:
      match ← f (path, md) state with
      | .done s => return .done s
      | .yield s =>
        state := s
        if isDir then
          if !(← w.prune path) then
            match ← forInRec w path state f with
            | .done s => return .done s
            | .yield s => state := s
    return .yield state
  catch _ =>
    return .yield init

instance : ForIn IO DirWalker (System.FilePath × Metadata) where
  forIn w init f := do
    match ← DirWalker.forInRec w w.root init f with
    | .done s => return s
    | .yield s => return s

def globFS (initDir : FilePath) (pattern : PatternValidated) : IO (Array String) := do
  let rootDir := initDir.toString
  let mut matched := #[]
  for (path, _) in ({ root := initDir : DirWalker }) do
    let relativePath := stripDirPrefix rootDir path.toString
    let pathSegments := (relativePath.splitOn "/").filter (!·.isEmpty)
    if matchSegments pattern.pattern pathSegments then
      matched := matched.push relativePath.toString
  return matched.qsort (· < ·)

def globWithDirMark (initDir : FilePath) (pattern : PatternValidated) : IO (Array String) := do
  let rootDir := initDir.toString
  let mut matched := #[]
  for (path, md) in ({ root := initDir : DirWalker }) do
    let mut relativePath := (stripDirPrefix rootDir path.toString).toString
    if md.type == FileType.dir && !relativePath.endsWith "/" then
      relativePath := relativePath ++ "/"
    let pathSegments := (relativePath.toRawSubstring.splitOn "/").filter (!·.isEmpty)
    if matchSegments pattern.pattern pathSegments then
      matched := matched.push relativePath
  return matched.qsort (· < ·)

def checkPattern (initDir : FilePath) (pattern : PatternValidated) : IO Bool := do
  let rootDir := initDir.toString
  for (path, _) in ({ root := initDir : DirWalker }) do
    let relativePath := stripDirPrefix rootDir path.toString
    let pathSegments := (relativePath.splitOn "/").filter (!·.isEmpty)
    if matchSegments pattern.pattern pathSegments then
      return true
  return false

def findByExtension (initDir : FilePath) (ext : String) : IO (Array String) := do
  let rootDir := initDir.toString
  let mut matched := #[]
  for (path, md) in ({ root := initDir : DirWalker }) do
    if md.type != FileType.dir then
      if path.extension == some ext then
        let relativePath := stripDirPrefix rootDir path.toString
        matched := matched.push relativePath.toString
  return matched.qsort (· < ·)

def findByExtensions (initDir : FilePath) (exts : Array String) : IO (Array String) := do
  let rootDir := initDir.toString
  let mut matched := #[]
  for (path, md) in ({ root := initDir : DirWalker }) do
    if md.type != FileType.dir then
      match path.extension with
      | some e =>
        if exts.contains e then
          let relativePath := stripDirPrefix rootDir path.toString
          matched := matched.push relativePath.toString
      | none => pure ()
  return matched.qsort (· < ·)

def findDirectories (initDir : FilePath) : IO (Array String) := do
  let rootDir := initDir.toString
  let mut matched := #[]
  for (path, md) in ({ root := initDir : DirWalker }) do
    if md.type == FileType.dir then
      let relativePath := stripDirPrefix rootDir path.toString
      matched := matched.push (relativePath.toString ++ "/")
  return matched.qsort (· < ·)

end
