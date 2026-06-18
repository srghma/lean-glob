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

def stripDotSlash (s : String) : String :=
  if s.startsWith "./" then s.drop 2 |>.toString else s

def findByExtension (ext : String) : IO (Array String) := do
  let res ← findRec "." fun p => p.extension == some ext
  let mut arr := res.map (fun p => stripDotSlash p.toString)
  return arr.qsort (· < ·)

def findByExtensions (exts : Array String) : IO (Array String) := do
  let res ← findRec "." fun p => match p.extension with
    | some e => exts.contains e
    | none => false
  let mut arr := res.map (fun p => stripDotSlash p.toString)
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

def findDirectories : IO (Array String) := do
  let res ← findDirsRec "."
  let mut arr := res.map (fun p => stripDotSlash p.toString ++ "/")
  return arr.qsort (· < ·)

end
