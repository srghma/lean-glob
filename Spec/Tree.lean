module
public import Tree
public import Init.System.IO

@[expose] public section

open System

def Tree_createAtPath : Tree → FilePath → IO Unit
  | Tree.file name, path => do
    let fullPath := path / name
    IO.FS.writeFile fullPath "" -- create empty file
  | Tree.dir name children, path => do
    let dirPath := path / name
    IO.FS.createDirAll dirPath
    for child in children do
      Tree_createAtPath child dirPath

def createAtPathForest (trees : List Tree) (path : FilePath) : IO Unit :=
  for tree in trees do
    Tree_createAtPath tree path

def withTempDirTree (t : Tree) (cont : FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun tmpDir => do Tree_createAtPath t tmpDir; cont tmpDir

def withTempDirForest (trees : List Tree) (cont : FilePath → IO α) : IO α :=
  IO.FS.withTempDir fun tmpDir => do createAtPathForest trees tmpDir; cont tmpDir

def withinTempDirTree (t : Tree) (cont : FilePath → IO α) : IO α :=
  withTempDirTree t (fun tmpDir => do IO.Process.setCurrentDir tmpDir; cont tmpDir)

def withinTempDirForest (ts : List Tree) (cont : FilePath → IO α) : IO α :=
  withTempDirForest ts (fun tmpDir => do IO.Process.setCurrentDir tmpDir; cont tmpDir)

end
