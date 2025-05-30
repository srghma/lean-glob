import Glob
import Init.Data.Repr
import Init.System.IO
import LSpec
import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Lean.Elab.Term
import Lean.Parser.Term
import Std.Data.HashSet
import Test.NormalizeReturnsIsValidSpec

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def main : IO Unit := return
