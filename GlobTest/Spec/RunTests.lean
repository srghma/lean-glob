module
public import Init.Data.Repr
public import Init.System.IO
public import Lean
public import Lean.Data.RBMap
public import Lean.Data.RBTree
public import Lean.Elab.Term
public import Lean.Parser.Term
public import Std.Data.HashSet
public import GlobTest.NormalizeReturnsIsValidSpec

@[expose] public section

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def withinTempDir (cont : IO α) : IO α := do
  withTempDir fun tmpDir => do
    IO.Process.setCurrentDir tmpDir
    IO.println s!"⏰ Running in temporary directory: {tmpDir}"
    cont

end
