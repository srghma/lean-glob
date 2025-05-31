import Glob
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
def assertGlobResult (name : String) (pattern : String) (tree : Tree) (expected : Option Tree) : IO Unit := do
  let patternValidated ← PatternValidated.patternStrictIO! pattern
  let actual := glob patternValidated tree
  unless actual == expected do
    IO.println s!"❌ {name} failed:"
    IO.println s!"  Pattern: {pattern}"
    IO.println s!"  Expected: {reprStr expected}"
    IO.println s!"  Actual: {reprStr actual}"
    throw <| IO.Error.userError s!"Assertion failed: {name}"

-- Helper to assert globMany results match expected Tree
def assertGlobManyResult (name : String) (patternsNel : NonEmptyList String) (tree : Tree) (expected : Option Tree) : IO Unit := do
  let patternsNel' ← patternsNel.mapM PatternValidated.patternStrictIO!
  let actual := globMany patternsNel' tree
  unless actual == expected do
    IO.println s!"❌ {name} failed:"
    IO.println s!"  Patterns: {patternsNel}"
    IO.println s!"  Expected: {reprStr expected}"
    IO.println s!"  Actual: {reprStr actual}"
    throw <| IO.Error.userError s!"Assertion failed: {name}"

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

  assertGlobResult "Glob root match" "Glob"
    (tree! "Glob" { "A" { } })
    (some (tree! "Glob" {}))

  assertGlobResult "Glob/A match" "Glob/A"
    (tree! "Glob" { "A" { } })
    (some (tree! "Glob" { "A" { } }))

  assertGlobResult "Glob/A match without children" "Glob/A"
    (tree! "Glob" { "A" })
    (some (tree! "Glob" { "A" }))

  assertGlobResult "Glob/B no match" "Glob/B"
    (tree! "Glob" { "A" { } })
    none

-- Wildcard tests
def testWildcardGlob : IO Unit := do
  IO.println "Testing wildcard patterns..."

  assertGlobResult "Double star match" "**"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } }))

  assertGlobResult "**/X recursive match" "**/X"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} } }))

  assertGlobResult "**/Y recursive match" "**/Y"
    globTestExample1
    (some (tree! "Glob" { "B" { "Y" {} } }))

  assertGlobResult "**/Z no match" "**/Z"
    globTestExample1
    none

  assertGlobResult "Glob/* single level" "Glob/*"
    globTestExample1
    (some (tree! "Glob" { "A" {}, "B" {} }))

  assertGlobResult "Glob/** recursive" "Glob/**"
    globTestExample1
    (some globTestExample1)

-- Specific path tests
def testSpecificPaths : IO Unit := do
  IO.println "Testing specific path patterns..."

  assertGlobResult "Glob/A/* match" "Glob/A/*"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} } }))

  assertGlobResult "Glob/A/** recursive" "Glob/A/**"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" { } } }))

  assertGlobResult "Glob/A/X exact match" "Glob/A/X"
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} } }))

  assertGlobResult "Glob/B/** recursive" "Glob/B/**"
    globTestExample1
    (some (tree! "Glob" { "B" { "Y" {} } }))

  assertGlobResult "Glob/C no match" "Glob/C"
    globTestExample1
    none

-- Simple tree tests
def testSimpleTrees : IO Unit := do
  IO.println "Testing simple tree patterns..."

  assertGlobResult "Single star match" "*"
    (tree! "foo" {})
    (some (tree! "foo" {}))

  assertGlobResult "Double star on simple tree" "**"
    (tree! "root" {})
    (some (tree! "root" {}))

-- Complex tree tests
def testComplexTree : IO Unit := do
  IO.println "Testing complex tree patterns..."

  assertGlobResult "**/baz.txt deep search" "**/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "**/delta.txt deep search" "**/delta.txt"
    globTestExample2
    (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

  assertGlobResult "**/file.txt search" "**/file.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "file.txt"  } }))

  assertGlobResult "**/qux.md search" "**/qux.md"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "qux.md" } } }))

  assertGlobResult "Root exact match" "Root"
    globTestExample2
    (some (tree! "Root" {}))

  assertGlobResult "Root/* first level" "Root/*"
    globTestExample2
    (some (Tree.dir "Root" [Tree.dir "foo" [], Tree.dir "foo2" [], Tree.dir "alpha" [], Tree.dir "zeta" []]))

  assertGlobResult "Root/** full tree" "Root/**"
    globTestExample2
    (some globTestExample2)

-- Multi-level pattern tests
def testMultiLevelPatterns : IO Unit := do
  IO.println "Testing multi-level patterns..."

  assertGlobResult "Root/**/bar/* nested wildcard" "Root/**/bar/*"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt", "qux.md" } }, "foo2" { "bar" { "baz2.txt", "qux2.md" } } }))

  assertGlobResult "Root/**/delta.txt deep nested" "Root/**/delta.txt"
    globTestExample2
    (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

  assertGlobResult "Root/**/file.txt nested search" "Root/**/file.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "file.txt"  } }))

  assertGlobResult "Root/*/*/*/delta.txt exact depth" "Root/*/*/*/delta.txt"
    globTestExample2
    (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

-- Specific path combinations
def testSpecificCombinations : IO Unit := do
  IO.println "Testing specific path combinations..."

  assertGlobResult "Root/foo/**/baz.txt" "Root/foo/**/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "Root/foo/*/baz.txt" "Root/foo/*/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "Root/foo/*/doesntexist.txt no match" "Root/foo/*/doesntexist.txt"
    globTestExample2
    none

  assertGlobResult "Root/foo/bar/baz.txt exact" "Root/foo/bar/baz.txt"
    globTestExample2
    (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))

  assertGlobResult "Root/foo/bar/baz.txt/extra invalid" "Root/foo/bar/baz.txt/extra"
    globTestExample2
    none

  assertGlobResult "Root/foo/bar/notfound.txt no match" "Root/foo/bar/notfound.txt"
    globTestExample2
    none

-- GlobMany tests using assertGlobManyResult
def testGlobMany : IO Unit := do
  IO.println "Testing globMany patterns..."

  assertGlobManyResult "GlobMany test 1" nel!["Glob/A", "Glob/B"]
    (tree! "Glob" { "A" {}, "B" {} })
    (some (tree! "Glob" { "A" {}, "B" {} }))

  assertGlobManyResult "GlobMany test 2" nel!["Glob/A", "Glob/C"]
    (tree! "Glob" { "A" {}, "B" {} })
    (some (tree! "Glob" { "A" {} }))

  assertGlobManyResult "GlobMany test 3" nel!["**/X", "**/Y"]
    globTestExample1
    (some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } }))

  assertGlobManyResult "GlobMany test 4" nel!["**/baz.txt", "**/delta.txt"]
    globTestExample2
    (some (tree! "Root" {
      "foo"   { "bar" { "baz.txt" } },
      "alpha" { "beta" { "gamma" { "delta.txt" } } }
    }))

  assertGlobManyResult "GlobMany test 5" nel!["**/file.txt", "**/qux.md"]
    globTestExample2
    (some (tree! "Root" { "foo" { "file.txt", "bar" { "qux.md" } } }))

  assertGlobManyResult "GlobMany test 6" nel!["**/doesntexist.txt", "**/missing.txt"]
    globTestExample2
    none

  assertGlobManyResult "GlobMany test 7" nel!["Root/foo/bar/baz.txt", "Root/foo2/bar/qux2.md"]
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

end
