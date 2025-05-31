import Glob.Data.Tree
import Init.System.IO

open System

def Tree.createAtPath : Tree → FilePath → IO Unit
  | Tree.file name, path => do
    let fullPath := path / name
    IO.FS.writeFile fullPath "" -- create empty file
  | Tree.dir name children, path => do
    let dirPath := path / name
    IO.FS.createDirAll dirPath
    for child in children do
      child.createAtPath dirPath

def createAtPathForest (trees : List Tree) (path : FilePath) : IO Unit :=
  for tree in trees do
    tree.createAtPath path

def withTempDirTree (t : Tree) (cont : FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun tmpDir => do t.createAtPath tmpDir; cont tmpDir

def withTempDirForest (trees : List Tree) (cont : FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun tmpDir => do createAtPathForest trees tmpDir; cont tmpDir

def withinTempDirTree (t : Tree) (cont : IO α) : IO α :=
  withTempDirTree t (do IO.Process.setCurrentDir ·; cont)

def withinTempDirForest (ts : List Tree) (cont : IO α) : IO α :=
  withTempDirForest ts (do IO.Process.setCurrentDir ·; cont)
