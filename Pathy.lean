/-
Copyright (c) 2024. All rights reserved.
Safe FilePath wrapper inspired by purescript-pathy
Provides type-safe path operations preventing invalid path constructions
-/

import Init.System.FilePath
import Init.Data.Option.Basic
import Init.Data.String.Basic
import Lean

namespace SafePath

/- inductive Platform where -/
/-   | Posix | Windows -/

-- Phantom types for path classification
inductive PathType where
  | Rel : PathType  -- Relative path
  | Abs : PathType  -- Absolute path

inductive FileType where
  | Dir  : FileType  -- Directory
  | File : FileType  -- File

-- The main Path type with phantom type parameters
structure Path (pathType : PathType) (fileType : FileType) where
  toFilePath : System.FilePath
  deriving Inhabited, DecidableEq, Hashable, Repr -- Ord

-- Type aliases for common path types
abbrev RelPath (ft : FileType) := Path PathType.Rel ft
abbrev AbsPath (ft : FileType) := Path PathType.Abs ft
abbrev RelDir := Path PathType.Rel FileType.Dir
abbrev AbsDir := Path PathType.Abs FileType.Dir
abbrev RelFile := Path PathType.Rel FileType.File
abbrev AbsFile := Path PathType.Abs FileType.File

-- Union types for paths that can be either absolute or relative
inductive AnyPath (ft : FileType) where
  | rel : RelPath ft → AnyPath ft
  | abs : AbsPath ft → AnyPath ft

abbrev AnyDir := AnyPath FileType.Dir
abbrev AnyFile := AnyPath FileType.File

-- Name type for path segments (non-empty strings)
structure Name (ft : FileType) where
  value : String
  nonEmpty : value ≠ ""
  deriving DecidableEq, Hashable, Repr, Ord

instance : Inhabited (Name (ft : FileType)) where
  default := ⟨"DEFAULT", by simp⟩

instance : ToString (Name ft) where
  toString n := n.value

def Name.fromString (s : String) : Option (Name ft) :=
  if h : s = "" then none else some ⟨s, h⟩

def Name.fromString! (s : String) : Name ft :=
  match Name.fromString s with
  | some n => n
  | none => panic! "Empty string provided to Name.fromString!"

-- Basic path constructors
def rootDir : AbsDir := ⟨"/"⟩

def currentDir : RelDir := ⟨"."⟩

-- File and directory constructors
def file (name : Name FileType.File) : RelFile := ⟨name.value⟩

def dir (name : Name FileType.Dir) : RelDir := ⟨name.value⟩

-- Path extension operator
def extendPath {pt : PathType} (base : Path pt FileType.Dir) (name : Name ft) : Path pt ft :=
  ⟨base.toFilePath / name.value⟩

infixl:65 " </> " => extendPath

-- Path appending (only relative paths can be appended)
def appendPath {pt : PathType} (base : Path pt FileType.Dir) (rel : RelPath ft) : Path pt ft :=
  ⟨System.FilePath.join base.toFilePath rel.toFilePath⟩

infixl:65 " <//> " => appendPath

-- Parent directory navigation
def parentOf (p : Path pt FileType.Dir) : Path pt FileType.Dir :=
  match p.toFilePath.parent with
  | some parent => ⟨parent⟩
  | none => p  -- Root directory case

-- Parent append (go up one level, then down into relative path)
def parentAppend {pt : PathType} (base : Path pt FileType.Dir) (rel : RelPath ft) : Path pt ft :=
  appendPath (parentOf base) rel

infixl:65 " <..> " => parentAppend

-- Path decomposition
structure PathComponents (pt : PathType) (ft : FileType) where
  parent : Path pt FileType.Dir
  name : Name ft
  deriving Hashable, Repr, DecidableEq, Inhabited -- Ord

def peel (p : Path pt ft) : Option (PathComponents pt ft) :=
  match p.toFilePath.parent, p.toFilePath.fileName with
  | some parent, some fname => Name.fromString fname |>.map (⟨⟨parent⟩, ·⟩)
  | _, _ => none

-- For files, we can guarantee peel will work (assuming valid construction)
def peelFile (p : Path pt FileType.File) : PathComponents pt FileType.File :=
  peel p |>.getD (panic! "Invalid file path in peelFile")

-- Get the name of the terminal segment
def name (p : Path pt ft) : Option (Name ft) := p.toFilePath.fileName >>= Name.fromString

-- For files, we can guarantee getting the name
def fileName (p : Path pt FileType.File) : Name FileType.File :=
  match name p with
  | some n => n
  | none => panic! "Invalid file path in fileName"

-- Path renaming
def rename (f : Name ft → Name ft) (p : Path pt ft) : Path pt ft :=
  match peel p with
  | some ⟨parent, oldName⟩ => parent </> f oldName
  | none => p

-- Extension handling
def setExtension (p : Path pt ft) (ext : String) : Path pt ft := ⟨p.toFilePath.withExtension ext⟩

infixl:65 " <.> " => setExtension

def addExtension (p : Path pt ft) (ext : String) : Path pt ft :=
  ⟨p.toFilePath.addExtension ext⟩

-- Convert absolute path to relative (relative to a base directory)
def relativeTo (target : AbsPath ft) (base : AbsDir) : RelPath ft :=
  -- This is a simplified implementation
  -- A full implementation would need proper path resolution
  ⟨System.FilePath.mk $ target.toFilePath.toString⟩

-- Path normalization
def normalize (p : Path pt ft) : Path pt ft := ⟨p.toFilePath.normalize⟩

-- Convert to System.FilePath for interop
def toFilePath (p : Path pt ft) : System.FilePath := p.toFilePath

-- Safe constructors from System.FilePath
def fromAbsoluteFilePath (fp : System.FilePath) (h : fp.isAbsolute) : AbsFile := ⟨fp⟩
def fromAbsoluteDirectory (fp : System.FilePath) (h : fp.isAbsolute) : AbsDir := ⟨fp⟩
def fromRelativeFilePath (fp : System.FilePath) (h : fp.isRelative) : RelFile := ⟨fp⟩
def fromRelativeDirectory (fp : System.FilePath) (h : fp.isRelative) : RelDir := ⟨fp⟩

#eval (System.FilePath.mk "a//b").normalize

-- Parsing functions that return Options for safety
def parseAbsFile (s : String) : Option AbsFile :=
  let fp := System.FilePath.mk s
  if fp.isAbsolute then some ⟨fp⟩ else none

def parseAbsDir (s : String) : Option AbsDir :=
  let fp := System.FilePath.mk s
  if fp.isAbsolute then some ⟨fp⟩ else none

def parseRelFile (s : String) : Option RelFile :=
  let fp := System.FilePath.mk s
  if fp.isRelative then some ⟨fp⟩ else none

def parseRelDir (s : String) : Option RelDir :=
  let fp := System.FilePath.mk s
  if fp.isRelative then some ⟨fp⟩ else none

-- String conversion
instance : ToString (Path pt ft) where
  toString p := p.toFilePath.toString

-- Useful helper functions
def isAbsolute : Path pt ft → Bool
  | ⟨fp⟩ => fp.isAbsolute

def isRelative : Path pt ft → Bool
  | ⟨fp⟩ => fp.isRelative

end SafePath

section

open _root_.IO (FileRight)
open _root_.IO.FS (DirEntry FileType Metadata Handle Mode)
open _root_.System (FilePath)

def SafePath.IO.FS.Handle.mk (fn : FilePath) (mode : Mode) : IO Handle := _root_.IO.FS.Handle.mk fn mode
def SafePath.IO.FS.realPath (fname : FilePath) : IO FilePath := _root_.IO.FS.realPath fname
def SafePath.IO.FS.removeFile (fname : FilePath) : IO Unit := _root_.IO.FS.removeFile fname
def SafePath.IO.FS.removeDir (p : FilePath) : IO Unit := _root_.IO.FS.removeDir p
def SafePath.IO.FS.createDir (p : FilePath) : IO Unit := _root_.IO.FS.createDir p
def SafePath.IO.FS.rename (old new : FilePath) : IO Unit := _root_.IO.FS.rename old new
def SafePath.IO.FS.createTempFile : IO (Handle × FilePath) := _root_.IO.FS.createTempFile
def SafePath.IO.FS.createTempDir : IO FilePath := _root_.IO.FS.createTempDir
def SafePath.IO.appPath : IO FilePath := _root_.IO.appPath
def SafePath.IO.currentDir : IO FilePath := _root_.IO.currentDir
def SafePath.IO.FS.withFile (fn : FilePath) (mode : Mode) (f : Handle → IO α) : IO α := _root_.IO.FS.withFile fn mode f
def SafePath.IO.FS.lines (fname : FilePath) : IO (Array String) := _root_.IO.FS.lines fname
def SafePath.IO.FS.writeBinFile (fname : FilePath) (content : ByteArray) : IO Unit := _root_.IO.FS.writeBinFile fname content
def SafePath.IO.FS.writeFile (fname : FilePath) (content : String) : IO Unit := _root_.IO.FS.writeFile fname content
def SafePath.IO.FS.DirEntry.path (entry : DirEntry) : FilePath := _root_.IO.FS.DirEntry.path entry
def SafePath.System.FilePath.readDir (p : FilePath) : IO (Array IO.FS.DirEntry) := _root_.System.FilePath.readDir p
def SafePath.System.FilePath.metadata (p : FilePath) : IO IO.FS.Metadata := _root_.System.FilePath.metadata p
def SafePath.System.FilePath.isDir (p : FilePath) : BaseIO Bool := _root_.System.FilePath.isDir p
def SafePath.System.FilePath.pathExists (p : FilePath) : BaseIO Bool := _root_.System.FilePath.pathExists p
def SafePath.System.FilePath.walkDir (p : FilePath) (enter : FilePath → IO Bool := fun _ => pure true) : IO (Array FilePath) := _root_.System.FilePath.walkDir p enter
def SafePath.IO.FS.readBinFile (fname : FilePath) : IO ByteArray := _root_.IO.FS.readBinFile fname
def SafePath.IO.FS.readFile (fname : FilePath) : IO String := _root_.IO.FS.readFile fname
def SafePath.IO.appDir : IO FilePath := _root_.IO.appDir
def SafePath.IO.FS.createDirAll (p : FilePath) : IO Unit := _root_.IO.FS.createDirAll p
def SafePath.IO.FS.removeDirAll (p : FilePath) : IO Unit := _root_.IO.FS.removeDirAll p
def SafePath.IO.FS.withTempFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : Handle → FilePath → m α) : m α := _root_.IO.FS.withTempFile f
def SafePath.IO.FS.withTempDir [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : FilePath → m α) : m α := _root_.IO.FS.withTempDir f
def SafePath.IO.Process.getCurrentDir : IO FilePath := _root_.IO.Process.getCurrentDir
def SafePath.IO.Process.setCurrentDir (path : FilePath) : IO Unit := _root_.IO.Process.setCurrentDir path
def SafePath.IO.Prim.setAccessRights (filename : FilePath) (mode : UInt32) : IO Unit := _root_.IO.Prim.setAccessRights filename mode
def SafePath.IO.setAccessRights (filename : FilePath) (mode : FileRight) : IO Unit := _root_.IO.setAccessRights filename mode

end
