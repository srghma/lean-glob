import Glob
import Glob.WF.IO
import Glob.WF.Tree
import Init.Data.Repr
import Init.System.IO
import LSpec
import Lean
import Lean.Data.RBMap
import Lean.Data.RBTree
import Lean.Elab.Term
import Lean.Parser.Term
import Std
import Std.Data.HashSet
import Test.GlobSpec
-- import Test.NormalizeReturnsIsValidSpec

open IO Lean
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

/--
`mkTestGlob pat t expected` returns a pair
```lean
  (testName, IO Unit)
where testName is derived from pat, and the IO Unit runs runGlobTest.

pat is the pattern string (the first argument to #testGlob)

t is the Tree to search in

expected is the Option Tree you expect back
-/
-- def main : IO Unit := return
def main : IO Unit := do
  GlobSpec.runGlobTests
  -- runTests #[
    -- ("FindRecursive", fun (currentTmpDir : FilePath) => do -- TODO: this is a limitation of glob-posix, no support of recursion
