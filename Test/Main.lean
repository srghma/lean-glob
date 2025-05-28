import Glob
import Init.System.IO
import Lean.Data.RBTree
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Lean.Parser.Term
import Init.Data.Repr
import Test.NormalizeReturnsIsValidSpec
import LSpec

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

def main : IO Unit := return
