module
public import Init.System.IO

@[expose] public section

open IO.FS
open System

partial def findRec (dir : FilePath) (filter : FilePath → Bool) : IO (Array FilePath) := do
  let mut result := #[]
  let entries ← dir.readDir
  for entry in entries do
    let path := entry.path
    let md ← path.metadata
    if md.type == FileType.dir then
      let sub ← findRec path filter
      result := result ++ sub
    else
      if filter path then
        result := result.push path
  return result

def stripDirPrefix (dir : String) (s : String) : String :=
  let pref := if dir == "." then "./" else dir ++ "/"
  if s.startsWith pref then s.drop pref.length |>.toString else s

def findByExtension (tmpDir : FilePath) (ext : String) : IO (Array String) := do
  let res ← findRec tmpDir.toString fun p => p.extension == some ext
  let mut arr := res.map (fun p => stripDirPrefix tmpDir.toString p.toString)
  return arr.qsort (· < ·)

def findByExtensions (tmpDir : FilePath) (exts : Array String) : IO (Array String) := do
  let res ← findRec tmpDir.toString fun p => match p.extension with
    | some e => exts.contains e
    | none => false
  let mut arr := res.map (fun p => stripDirPrefix tmpDir.toString p.toString)
  return arr.qsort (· < ·)

partial def findDirsRec (dir : FilePath) : IO (Array FilePath) := do
  let mut result := #[]
  let entries ← dir.readDir
  for entry in entries do
    let path := entry.path
    let md ← path.metadata
    if md.type == FileType.dir then
      result := result.push path
      let sub ← findDirsRec path
      result := result ++ sub
  return result

def findDirectories (tmpDir : FilePath) : IO (Array String) := do
  let res ← findDirsRec tmpDir.toString
  let mut arr := res.map (fun p => stripDirPrefix tmpDir.toString p.toString ++ "/")
  return arr.qsort (· < ·)

end
