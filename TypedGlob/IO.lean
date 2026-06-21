module
public import Init.System.IO
public import Lean
public import Glob.NonWF.Types
public import Glob.WF.Types
public import Glob.WF.IO
public import TypedGlob.Class

@[expose] public section

open NonEmpty.String NonEmpty.List
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

-- generic typed globbing functions
def typedGlobFS [IsTypedPath P] (initDir : P) (pattern : PatternValidated) : IO (Array P) := do
  let rootDir := IsTypedPath.toString initDir
  let mut matched := #[]
  for (path, _) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    let relativePath := stripDirPrefix rootDir path.toString
    let pathSegments := (relativePath.split (· == '/')).filter (!·.isEmpty) |>.toList
    if matchSegments pattern.pattern pathSegments then
      match IsTypedPath.parseValid (P:=P) (ToString.toString relativePath) with
      | some p => matched := matched.push p
      | none => pure ()
  return matched.qsort (fun a b => IsTypedPath.toString a < IsTypedPath.toString b)

def typedGlobWithDirMark [IsTypedPath P] (initDir : P) (pattern : PatternValidated) : IO (Array P) := do
  let rootDir := IsTypedPath.toString initDir
  let mut matched := #[]
  for (path, md) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    let mut relativePath := ToString.toString (stripDirPrefix rootDir path.toString)
    if md.type == FileType.dir && !relativePath.endsWith "/" then
      relativePath := relativePath ++ "/"
    let pathSegments := (relativePath.toSlice.split (· == '/')).filter (!·.isEmpty) |>.toList
    if matchSegments pattern.pattern pathSegments then
      match IsTypedPath.parseValid (P:=P) relativePath with
      | some p => matched := matched.push p
      | none => pure ()
  return matched.qsort (fun a b => IsTypedPath.toString a < IsTypedPath.toString b)

def typedCheckPattern [IsTypedPath P] (initDir : P) (pattern : PatternValidated) : IO Bool := do
  let rootDir := IsTypedPath.toString initDir
  for (path, _) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    let relativePath := stripDirPrefix rootDir path.toString
    let pathSegments := (relativePath.split (· == '/')).filter (!·.isEmpty) |>.toList
    if matchSegments pattern.pattern pathSegments then
      return true
  return false

def typedFindByExtension [IsTypedPath P] (initDir : P) (ext : String) : IO (Array P) := do
  let rootDir := IsTypedPath.toString initDir
  let mut matched := #[]
  for (path, md) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    if md.type != FileType.dir then
      if path.extension == some ext then
        let relativePath := ToString.toString (stripDirPrefix rootDir path.toString)
        match IsTypedPath.parseValid (P:=P) relativePath with
        | some p => matched := matched.push p
        | none => pure ()
  return matched.qsort (fun a b => IsTypedPath.toString a < IsTypedPath.toString b)

def typedFindByExtensions [IsTypedPath P] (initDir : P) (exts : Array String) : IO (Array P) := do
  let rootDir := IsTypedPath.toString initDir
  let mut matched := #[]
  for (path, md) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    if md.type != FileType.dir then
      match path.extension with
      | some e =>
        if exts.contains e then
          let relativePath := ToString.toString (stripDirPrefix rootDir path.toString)
          match IsTypedPath.parseValid (P:=P) relativePath with
          | some p => matched := matched.push p
          | none => pure ()
      | none => pure ()
  return matched.qsort (fun a b => IsTypedPath.toString a < IsTypedPath.toString b)

def typedFindDirectories [IsTypedPath P] (initDir : P) : IO (Array P) := do
  let rootDir := IsTypedPath.toString initDir
  let mut matched := #[]
  for (path, md) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    if md.type == FileType.dir then
      let relativePath := ToString.toString (stripDirPrefix rootDir path.toString) ++ "/"
      match IsTypedPath.parseValid (P:=P) relativePath with
      | some p => matched := matched.push p
      | none => pure ()
  return matched.qsort (fun a b => IsTypedPath.toString a < IsTypedPath.toString b)

def typedGlobDirsOnly [IsTypedPath P] (initDir : P) (pattern : PatternValidated) : IO (Array P) := do
  let rootDir := IsTypedPath.toString initDir
  let mut matched := #[]
  for (path, md) in ({ root := IsTypedPath.toFilePath initDir : DirWalker }) do
    if md.type == FileType.dir then
      let relativePath := stripDirPrefix rootDir path.toString
      let pathSegments := (relativePath.split (· == '/')).filter (!·.isEmpty) |>.toList
      if matchSegments pattern.pattern pathSegments then
        let relativeStr := ToString.toString relativePath ++ "/"
        match IsTypedPath.parseValid (P:=P) relativeStr with
        | some p => matched := matched.push p
        | none => pure ()
  return matched.qsort (fun a b => IsTypedPath.toString a < IsTypedPath.toString b)

end
