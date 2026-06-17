module
public import Glob
public import Glob.WF.IO
public import Glob.WF.Tree
public import Init.Data.Repr
public import Init.System.IO
public import LSpec
public import Lean
public import Lean.Data.RBMap
public import Lean.Data.RBTree
public import Lean.Elab.Term
public import Lean.Parser.Term
public import Std
public import Std.Data.HashSet
public import GlobTest.GlobSpec
public import GlobTest.GlobRealSpec

@[expose] public section

open IO Lean
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

/--
`mkTestGlob pat t expected` returns a pair
```lean
  (testName, IO Unit)
```

where testName is derived from pat, and the IO Unit runs runGlobTest.

pat is the pattern string (the first argument to #testGlob)

t is the Tree to search in

expected is the Option Tree you expect back
-/

-- def main : IO Unit := return
def main : IO Unit := do
  GlobSpec.runGlobTests
  runGlobRealTests
  -- runTests #[
  -- ("FindRecursive", fun (currentTmpDir : FilePath) => do -- TODO: this is a limitation of glob-posix, no support of recursion

end
