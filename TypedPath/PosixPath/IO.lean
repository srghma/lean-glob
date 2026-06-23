module
public import TypedPath.PosixPath


@[expose] public section

namespace Posix.IO

open Posix (PosixPath AnyPosixPath parsePosixPath parsePosixPathAuto ExpectedPosixPath Config ParseError)

abbrev AnyFile ap pt ac := PosixPath ap pt .File ac
abbrev AnyDir ap pt ac := PosixPath ap pt .Dir ac
abbrev AnyPath ap pt ac ft := PosixPath ap pt ft ac

abbrev AbsFile := PosixPath false .Abs .File false
abbrev AbsDir  := PosixPath false .Abs .Dir false

def _root_.Posix.PosixPath.toFilePath {ap pt ft ac} (p : PosixPath ap pt ft ac) : _root_.System.FilePath :=
  ⟨toString p⟩

open _root_.System (FilePath)
open _root_.IO.FS (Handle Mode DirEntry Metadata)

instance (ft : FileType) : Inhabited (PosixPath false .Abs ft false) :=
  match ft with
  | .Dir => ⟨posixPath! "/dummy/"⟩
  | .File => ⟨posixPath! "/dummy"⟩

def fileTypeToString (ft : FileType) : String :=
  match ft with
  | .Dir => "Dir"
  | .File => "File"

/-- Wrap a `FilePath` the OS handed back. `panic!`s if it violates expectations. -/
def wrapAbs! (ft : FileType) (fp : FilePath) : PosixPath false .Abs ft false :=
  match parsePosixPathAuto fp.toString with
  | Except.ok ⟨allowCwd, allowParents, pathType, fileType, p⟩ =>
      if h1 : fileType = ft then
        if h2 : pathType = .Abs then
          if h3 : allowParents = false then
            if h4 : allowCwd = false then
              cast (by rw [h1, h2, h3, h4]) p
            else
              panic! s!"PosixPath.IO: expected no cwd, OS returned {fp}"
          else
            panic! s!"PosixPath.IO: expected no parents, OS returned {fp}"
        else
          panic! s!"PosixPath.IO: expected an absolute path, OS returned {fp}"
      else
        panic! s!"PosixPath.IO: expected a {fileTypeToString ft} path, OS returned {fp}"
  | Except.error e => panic! s!"PosixPath.IO: OS returned unparseable path {fp}: {e}"

def wrapAbsFile! (fp : FilePath) : AbsFile := wrapAbs! .File fp
def wrapAbsDir!  (fp : FilePath) : AbsDir  := wrapAbs! .Dir fp

variable {ap : Bool} {pt : PathType} {ac : Bool} {ft : FileType}

def Handle.mk (fn : AnyFile ap pt ac) (mode : Mode) : _root_.IO Handle :=
  _root_.IO.FS.Handle.mk fn.toFilePath mode

def realPath (fname : AnyPath ap pt ac ft) : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.FS.realPath fname.toFilePath

def removeFile (fname : AnyFile ap pt ac) : _root_.IO Unit :=
  _root_.IO.FS.removeFile fname.toFilePath

def removeDir (p : AnyDir ap pt ac) : _root_.IO Unit :=
  _root_.IO.FS.removeDir p.toFilePath

def createDir (p : AnyDir ap pt ac) : _root_.IO Unit :=
  _root_.IO.FS.createDir p.toFilePath

def rename (old new : AnyPath ap pt ac ft) : _root_.IO Unit :=
  _root_.IO.FS.rename old.toFilePath new.toFilePath

def createTempFile : _root_.IO (Handle × AbsFile) := do
  let (h, fp) ← _root_.IO.FS.createTempFile
  return (h, wrapAbsFile! fp)

def createTempDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.FS.createTempDir

def appPath : _root_.IO AbsFile :=
  wrapAbsFile! <$> _root_.IO.appPath

def currentDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.currentDir

def withFile (fn : AnyFile ap pt ac) (mode : Mode) (f : Handle → _root_.IO α) : _root_.IO α :=
  _root_.IO.FS.withFile fn.toFilePath mode f

def lines (fname : AnyFile ap pt ac) : _root_.IO (Array String) :=
  _root_.IO.FS.lines fname.toFilePath

def writeBinFile (fname : AnyFile ap pt ac) (content : ByteArray) : _root_.IO Unit :=
  _root_.IO.FS.writeBinFile fname.toFilePath content

def writeFile (fname : AnyFile ap pt ac) (content : String) : _root_.IO Unit :=
  _root_.IO.FS.writeFile fname.toFilePath content

def DirEntry.path (entry : DirEntry) : AbsFile :=
  wrapAbsFile! (_root_.IO.FS.DirEntry.path entry)

structure PosixDirEntry {ap : Bool} {pt : PathType} {ac : Bool} where
  root     : AnyDir ap pt ac
  fileName : PosixNormalComponent

def PosixDirEntry.path (e : PosixDirEntry (ap:=ap) (pt:=pt) (ac:=ac)) (ft : FileType) : Except String (PosixPath ap pt ft ac) :=
  let fpStr := (e.root.toFilePath / e.fileName.toNonEmptyString.toString).toString
  let fpStrWithSlash := match ft with
    | .Dir => fpStr ++ "/"
    | .File => fpStr
  match parsePosixPathAuto fpStrWithSlash with
  | Except.ok ⟨allowCwd, allowParents, pathType, fileType, p⟩ =>
      if h1 : fileType = ft then
        if h2 : pathType = pt then
          if h3 : allowParents = ap then
            if h4 : allowCwd = ac then
              Except.ok (cast (by rw [h1, h2, h3, h4]) p)
            else
              Except.error s!"PosixPath.IO: expected allowCwd {ac}, OS returned {fpStrWithSlash}"
          else
            Except.error s!"PosixPath.IO: expected allowParents {ap}, OS returned {fpStrWithSlash}"
        else
          Except.error s!"PosixPath.IO: expected correct pathType, OS returned {fpStrWithSlash}"
      else
        Except.error s!"PosixPath.IO: expected correct fileType, OS returned {fpStrWithSlash}"
  | Except.error err => Except.error s!"PosixPath.IO: OS returned unparseable path {fpStrWithSlash}: {err}"

def PosixDirEntry.metadata (e : PosixDirEntry (ap:=ap) (pt:=pt) (ac:=ac)) : _root_.IO _root_.IO.FS.Metadata :=
  _root_.System.FilePath.metadata (e.root.toFilePath / e.fileName.toNonEmptyString.toString)

def readDir (p : AnyDir ap pt ac) : _root_.IO (Array (PosixDirEntry (ap:=ap) (pt:=pt) (ac:=ac))) := do
  let entries ← _root_.System.FilePath.readDir p.toFilePath
  return entries.map (fun e => { root := p, fileName := (PosixNormalComponent.mk? e.fileName).get! })

-- def mapMParallel {α β : Type} (f : α → _root_.IO β) (as : Array α) : _root_.IO (Array β) := do
--   let tasks ← as.mapM fun a => _root_.IO.asTask (f a)
--   Array.zip (Array.range as.size) tasks
--   |> Array.mapM (fun (_, t) => t.get)

-- TODO: in parallel. But actually dont use it
def readDirWithMetadata (p : AnyDir ap pt ac) : _root_.IO (Array (PosixDirEntry (ap:=ap) (pt:=pt) (ac:=ac) × _root_.IO.FS.Metadata)) := do
  let entries ← readDir p
  entries.mapM (fun e => do
    let md ← e.metadata
    return (e, md))

-- #eval show _root_.IO Unit from do
--   let td ← _root_.IO.FS.createTempDir
--   _root_.IO.FS.createDir (td / "foo")
--   _root_.IO.FS.writeFile (td / "foo" / "test.txt") ""

--   _root_.IO.Process.setCurrentDir td
--   let entriesRel ← _root_.System.FilePath.readDir "foo"
--   if let some e := entriesRel[0]? then
--     if e.root.toString != "foo" then throw (_root_.IO.userError s!"Expected foo, got {e.root}")

--   _root_.IO.Process.setCurrentDir (td / "foo")
--   let entriesDot ← _root_.System.FilePath.readDir "."
--   if let some e := entriesDot[0]? then
--     if e.root.toString != "." then throw (_root_.IO.userError s!"Expected ., got {e.root}")

--   _root_.IO.Process.setCurrentDir (td / "foo")
--   let entriesDotDot ← _root_.System.FilePath.readDir ".."
--   if let some e := entriesDotDot.find? (fun e => e.fileName == "foo") then
--     if e.root.toString != ".." then throw (_root_.IO.userError s!"Expected .., got {e.root}")

def metadata (p : AnyPath ap pt ac ft) : _root_.IO Metadata :=
  _root_.System.FilePath.metadata p.toFilePath

def isDir (p : AnyPath ap pt ac ft) : BaseIO Bool :=
  _root_.System.FilePath.isDir p.toFilePath

def pathExists (p : AnyPath ap pt ac ft) : BaseIO Bool :=
  _root_.System.FilePath.pathExists p.toFilePath

def walkDir (p : AnyDir ap pt ac) (enter : FilePath → _root_.IO Bool := fun _ => pure true) :
    _root_.IO (Array FilePath) :=
  _root_.System.FilePath.walkDir p.toFilePath enter

def readBinFile (fname : AnyFile ap pt ac) : _root_.IO ByteArray :=
  _root_.IO.FS.readBinFile fname.toFilePath

def readFile (fname : AnyFile ap pt ac) : _root_.IO String :=
  _root_.IO.FS.readFile fname.toFilePath

def appDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.appDir

def createDirAll (p : AnyDir ap pt ac) : _root_.IO Unit :=
  _root_.IO.FS.createDirAll p.toFilePath

def removeDirAll (p : AnyDir ap pt ac) : _root_.IO Unit :=
  _root_.IO.FS.removeDirAll p.toFilePath

def withTempFile [Monad m] [MonadFinally m] [MonadLiftT _root_.IO m]
    (f : Handle → AbsFile → m α) : m α :=
  _root_.IO.FS.withTempFile (fun h fp => f h (wrapAbsFile! fp))

def withTempDir [Monad m] [MonadFinally m] [MonadLiftT _root_.IO m]
    (f : AbsDir → m α) : m α :=
  _root_.IO.FS.withTempDir (fun fp => f (wrapAbsDir! fp))

def getCurrentDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.Process.getCurrentDir

def setCurrentDir (path : AnyDir ap pt ac) : _root_.IO Unit :=
  _root_.IO.Process.setCurrentDir path.toFilePath

def setAccessRightsPrim (filename : AnyPath ap pt ac ft) (mode : UInt32) : _root_.IO Unit :=
  _root_.IO.Prim.setAccessRights filename.toFilePath mode

end Posix.IO
