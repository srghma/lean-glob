import Glob
import Glob.Data.NonEmptyList
import Glob.Data.Tree
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
import Std.Data.HashSet
import Test.NormalizeReturnsIsValidSpec
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

namespace GlobSpec

-- Updated function signatures to match the actual glob functions
def glob (pattern : PatternValidated) (tree : Tree) : Option Tree := none
def globMany (patterns : NonEmptyList PatternValidated) (tree : Tree) : Option Tree := none

-- Helper to assert glob results match expected Tree
def assertGlobResult (pattern : String) (tree : Tree) (expected : Option Tree) : IO Unit := do
  let patternValidated ← PatternValidated.patternStrictIO! pattern
  let actual := glob patternValidated tree
  unless actual == expected do
    IO.println s!"❌ {pattern} failed:"
    IO.println s!"  Pattern: {pattern}"
    IO.println s!"  Expected: {reprStr expected}"
    IO.println s!"  Actual: {reprStr actual}"
    throw <| IO.Error.userError s!"Assertion failed: {pattern}"

-- Helper to assert globMany results match expected Tree
def assertGlobManyResult (patternsNel : NonEmptyList String) (tree : Tree) (expected : Option Tree) : IO Unit := do
  let patternsNel' ← patternsNel.mapM PatternValidated.patternStrictIO!
  let actual := globMany patternsNel' tree
  unless actual == expected do
    IO.println s!"❌ {toString patternsNel} failed:"
    IO.println s!"  Patterns: {patternsNel}"
    IO.println s!"  Expected: {reprStr expected}"
    IO.println s!"  Actual: {reprStr actual}"
    throw <| IO.Error.userError s!"Assertion failed: {toString patternsNel}"

-- Test data
def globTestExample1 := tree! "Glob" { "A" { "X" { } }, "B" { "Y" { } } }

def globTestExample2 := tree! "Root" {
  "foo" { "file.txt", "bar" { "baz.txt" , "qux.md" } },
  "foo2" { "file2.txt", "bar" { "baz2.txt", "qux2.md" }  },
  "alpha" { "beta" { "gamma" { "delta.txt"  } } },
  "zeta" {}
}

-- Basic glob tests
def testBasicGlob : IO Unit := do
  IO.println "Testing basic glob patterns..."

  assertGlobResult "Glob"
    (tree! "Glob" { "A" { } })
    (some (tree! "Glob" {}))

  assertGlobResult "Glob/A"
    (tree! "Glob" { "A" { } })
    (some (tree! "Glob" { "A" { } }))

  assertGlobResult "Glob/A"
    (tree! "Glob" { "A" })
    (some (tree! "Glob" { "A" }))

  assertGlobResult "Glob/B"
    (tree! "Glob" { "A" { } })
    none

-- Wildcard tests
def testWildcardGlob : IO Unit := do
  IO.println "Testing wildcard patterns..."

  assertGlobResult "**"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } }))

  assertGlobResult "**/X"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} } }))

  assertGlobResult "**/Y"
    globTestExample1
    (some (tree! "Glob" { "B" { "Y" {} } }))

  assertGlobResult "**/Z"
    globTestExample1
    none

  assertGlobResult "Glob/*"
    globTestExample1
    (some (tree! "Glob" { "A" {}, "B" {} }))

  assertGlobResult "Glob/**"
    globTestExample1
    (some globTestExample1)

-- Specific path tests
def testSpecificPaths : IO Unit := do
  IO.println "Testing specific path patterns..."

  assertGlobResult "Glob/A/*"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} } }))

  assertGlobResult "Glob/A/**"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" { } } }))

  assertGlobResult "Glob/A/X"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} } }))

  assertGlobResult "Glob/B/**"
    globTestExample1
    (some (tree! "Glob" { "B" { "Y" {} } }))

  assertGlobResult "Glob/C"
    globTestExample1
    none

-- Simple tree tests
def testSimpleTrees : IO Unit := do
  IO.println "Testing simple tree patterns..."

  assertGlobResult "*"
    (tree! "foo" {})
    (some (tree! "foo" {}))

  assertGlobResult "**"
    (tree! "root" {})
    (some (tree! "root" {}))

-- Complex tree tests
def testComplexTree : IO Unit := do
  IO.println "Testing complex tree patterns..."

  assertGlobResult "**/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "**/delta.txt"
    globTestExample2
    (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

  assertGlobResult "**/file.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "file.txt"  } }))

  assertGlobResult "**/qux.md"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "qux.md" } } }))

  assertGlobResult "Root"
    globTestExample2
    (some (tree! "Root" {}))

  assertGlobResult "Root/*"
    globTestExample2
    (some (Tree.dir "Root" [Tree.dir "foo" [], Tree.dir "foo2" [], Tree.dir "alpha" [], Tree.dir "zeta" []]))

  assertGlobResult "Root/**"
    globTestExample2
    (some globTestExample2)

-- Multi-level pattern tests
def testMultiLevelPatterns : IO Unit := do
  IO.println "Testing multi-level patterns..."

  assertGlobResult "Root/**/bar/*"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt", "qux.md" } }, "foo2" { "bar" { "baz2.txt", "qux2.md" } } }))

  assertGlobResult "Root/**/delta.txt"
    globTestExample2
    (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

  assertGlobResult "Root/**/file.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "file.txt"  } }))

  assertGlobResult "Root/*/*/*/delta.txt"
    globTestExample2
    (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

-- Specific path combinations
def testSpecificCombinations : IO Unit := do
  IO.println "Testing specific path combinations..."

  assertGlobResult "Root/foo/**/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "Root/foo/*/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "Root/foo/*/doesntexist.txt"
    globTestExample2
    none

  assertGlobResult "Root/foo/bar/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "Root/foo/bar/baz.txt/extra"
    globTestExample2
    none

  assertGlobResult "Root/foo/bar/notfound.txt"
    globTestExample2
    none

-- GlobMany tests using assertGlobManyResult
def testGlobMany : IO Unit := do
  IO.println "Testing globMany patterns..."

  assertGlobManyResult nel!["Glob/A", "Glob/B"] (tree! "Glob" { "A" {}, "B" {} }) (some (tree! "Glob" { "A" {}, "B" {} }))
  assertGlobManyResult nel!["Glob/A", "Glob/C"] (tree! "Glob" { "A" {}, "B" {} }) (some (tree! "Glob" { "A" {} }))
  assertGlobManyResult nel!["**/X", "**/Y"] globTestExample1 (some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } }))
  assertGlobManyResult nel!["**/baz.txt", "**/delta.txt"]
    globTestExample2
    (some (tree! "Root" {
      "foo"   { "bar" { "baz.txt" } },
      "alpha" { "beta" { "gamma" { "delta.txt" } } }
    }))

  assertGlobManyResult nel!["**/file.txt", "**/qux.md"] globTestExample2 (some (tree! "Root" { "foo" { "file.txt", "bar" { "qux.md" } } }))

  assertGlobManyResult nel!["**/doesntexist.txt", "**/missing.txt"] globTestExample2 none

  assertGlobManyResult nel!["Root/foo/bar/baz.txt", "Root/foo2/bar/qux2.md"]
    globTestExample2
    (some (tree! "Root" {
      "foo"  { "bar" { "baz.txt" } },
      "foo2" { "bar" { "qux2.md" } }
    }))

-- Main test runner
def runGlobTests : IO Unit := do
  IO.println "🧪 Starting Glob Pattern Tests..."

  try
    testBasicGlob
    testWildcardGlob
    testSpecificPaths
    testSimpleTrees
    testComplexTree
    testMultiLevelPatterns
    testSpecificCombinations
    testGlobMany

    IO.println "✅ All glob pattern tests passed!"
  catch e =>
    IO.println s!"❌ Glob tests failed: {e}"
    throw e

end GlobSpec
