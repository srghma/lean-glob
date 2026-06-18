module
public import Glob
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
public import Glob.Data.Tree
public import Glob.WF.IO
public import Glob.WF.Tree
public import Init.Data.Repr
public import Init.System.IO
public import Lean
public import GlobTest.NormalizeReturnsIsValidSpec
public import GlobTest.Spec.Core

@[expose] public section

open NonEmpty.String NonEmpty.List
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)
open GlobTest.Spec.Core

namespace GlobSpec

-- Helper to assert glob results match expected Tree
def assertGlobResult (pattern : String) (tree : Tree) (expected : Option Tree) : IO Unit := do
  let patternValidated ← PatternValidated.patternStrictIO! pattern
  let actual := Glob.globValidated patternValidated tree
  unless actual == expected do
    throw <| IO.Error.userError s!"{pattern}: expected {reprStr expected}, got {reprStr actual}"

-- Helper to assert globMany results match expected Tree
def assertGlobManyResult (patternsNel : NonEmptyList String) (tree : Tree) (expected : Option Tree) : IO Unit := do
  let patternsNel' ← patternsNel.mapM PatternValidated.patternStrictIO!
  let actual := Glob.globManyValidated patternsNel' tree
  unless actual == expected do
    throw <| IO.Error.userError s!"{toString patternsNel}: expected {reprStr expected}, got {reprStr actual}"

-- Test data
def globTestExample1 := tree! "Glob" { "A" { "X" { } }, "B" { "Y" { } } }

def globTestExample2 := tree! "Root" {
  "foo" { "file.txt", "bar" { "baz.txt" , "qux.md" } },
  "foo2" { "file2.txt", "bar" { "baz2.txt", "qux2.md" }  },
  "alpha" { "beta" { "gamma" { "delta.txt"  } } },
  "zeta" {}
}

def spec : Spec := do
  describe "Glob" do
    describe "basic patterns" do
      it "matches a directory, dropping children" do
        assertGlobResult "Glob"
          (tree! "Glob" { "A" { } })
          (some (tree! "Glob" {}))
      it "matches a nested directory" do
        assertGlobResult "Glob/A"
          (tree! "Glob" { "A" { } })
          (some (tree! "Glob" { "A" { } }))
      it "matches a leaf directory" do
        assertGlobResult "Glob/A"
          (tree! "Glob" { "A" })
          (some (tree! "Glob" { "A" }))
      it "returns none when no match" do
        assertGlobResult "Glob/B"
          (tree! "Glob" { "A" { } })
          none

    describe "wildcards" do
      it "** matches everything" do
        assertGlobResult "**"
          globTestExample1
          (some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } }))
      it "**/X selects X branches" do
        assertGlobResult "**/X"
          globTestExample1
          (some (tree! "Glob" { "A" { "X" {} } }))
      it "**/Y selects Y branches" do
        assertGlobResult "**/Y"
          globTestExample1
          (some (tree! "Glob" { "B" { "Y" {} } }))
      it "**/Z matches nothing" do
        assertGlobResult "**/Z"
          globTestExample1
          none
      it "Glob/* matches immediate children" do
        assertGlobResult "Glob/*"
          globTestExample1
          (some (tree! "Glob" { "A" {}, "B" {} }))
      it "Glob/** matches whole subtree" do
        assertGlobResult "Glob/**"
          globTestExample1
          (some globTestExample1)

    describe "specific paths" do
      it "Glob/A/*" do
        assertGlobResult "Glob/A/*"
          globTestExample1
          (some (tree! "Glob" { "A" { "X" { } } }))
      it "Glob/A/**" do
        assertGlobResult "Glob/A/**"
          globTestExample1
          (some (tree! "Glob" { "A" { "X" { } } }))
      it "Glob/A/X" do
        assertGlobResult "Glob/A/X"
          globTestExample1
          (some (tree! "Glob" { "A" { "X" {} } }))
      it "Glob/B/**" do
        assertGlobResult "Glob/B/**"
          globTestExample1
          (some (tree! "Glob" { "B" { "Y" {} } }))
      it "Glob/C returns none" do
        assertGlobResult "Glob/C"
          globTestExample1
          none

    describe "simple trees" do
      it "* matches single node" do
        assertGlobResult "*"
          (tree! "foo" {})
          (some (tree! "foo" {}))
      it "** matches single root" do
        assertGlobResult "**"
          (tree! "root" {})
          (some (tree! "root" {}))

    describe "complex tree" do
      it "**/baz.txt" do
        assertGlobResult "**/baz.txt"
          globTestExample2
          (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))
      it "**/delta.txt" do
        assertGlobResult "**/delta.txt"
          globTestExample2
          (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))
      it "**/file.txt" do
        assertGlobResult "**/file.txt"
          globTestExample2
          (some (tree! "Root" { "foo" { "file.txt"  } }))
      it "**/qux.md" do
        assertGlobResult "**/qux.md"
          globTestExample2
          (some (tree! "Root" { "foo" { "bar" { "qux.md" } } }))
      it "Root" do
        assertGlobResult "Root"
          globTestExample2
          (some (tree! "Root" {}))
      it "Root/*" do
        assertGlobResult "Root/*"
          globTestExample2
          (some (Tree.dir "Root" [Tree.dir "foo" [], Tree.dir "foo2" [], Tree.dir "alpha" [], Tree.dir "zeta" []]))
      it "Root/**" do
        assertGlobResult "Root/**"
          globTestExample2
          (some globTestExample2)

    describe "multi-level patterns" do
      it "Root/**/bar/*" do
        assertGlobResult "Root/**/bar/*"
          globTestExample2
          (some (tree! "Root" { "foo" { "bar" { "baz.txt", "qux.md" } }, "foo2" { "bar" { "baz2.txt", "qux2.md" } } }))
      it "Root/**/delta.txt" do
        assertGlobResult "Root/**/delta.txt"
          globTestExample2
          (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))
      it "Root/**/file.txt" do
        assertGlobResult "Root/**/file.txt"
          globTestExample2
          (some (tree! "Root" { "foo" { "file.txt"  } }))
      it "Root/*/*/*/delta.txt" do
        assertGlobResult "Root/*/*/*/delta.txt"
          globTestExample2
          (some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } }))

    describe "specific combinations" do
      it "Root/foo/**/baz.txt" do
        assertGlobResult "Root/foo/**/baz.txt"
          globTestExample2
          (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))
      it "Root/foo/*/baz.txt" do
        assertGlobResult "Root/foo/*/baz.txt"
          globTestExample2
          (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))
      it "Root/foo/*/doesntexist.txt" do
        assertGlobResult "Root/foo/*/doesntexist.txt"
          globTestExample2
          none
      it "Root/foo/bar/baz.txt" do
        assertGlobResult "Root/foo/bar/baz.txt"
          globTestExample2
          (some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } }))
      it "Root/foo/bar/baz.txt/extra" do
        assertGlobResult "Root/foo/bar/baz.txt/extra"
          globTestExample2
          none
      it "Root/foo/bar/notfound.txt" do
        assertGlobResult "Root/foo/bar/notfound.txt"
          globTestExample2
          none

    describe "globMany" do
      it "Glob/A + Glob/B" do
        assertGlobManyResult !["Glob/A", "Glob/B"] (tree! "Glob" { "A" {}, "B" {} }) (some (tree! "Glob" { "A" {}, "B" {} }))
      it "Glob/A + Glob/C (partial)" do
        assertGlobManyResult !["Glob/A", "Glob/C"] (tree! "Glob" { "A" {}, "B" {} }) (some (tree! "Glob" { "A" {} }))
      it "**/X + **/Y" do
        assertGlobManyResult !["**/X", "**/Y"] globTestExample1 (some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } }))
      it "**/baz.txt + **/delta.txt" do
        assertGlobManyResult !["**/baz.txt", "**/delta.txt"]
          globTestExample2
          (some (tree! "Root" {
            "foo"   { "bar" { "baz.txt" } },
            "alpha" { "beta" { "gamma" { "delta.txt" } } }
          }))
      it "**/file.txt + **/qux.md" do
        assertGlobManyResult !["**/file.txt", "**/qux.md"] globTestExample2 (some (tree! "Root" { "foo" { "file.txt", "bar" { "qux.md" } } }))
      it "no matches yields none" do
        assertGlobManyResult !["**/doesntexist.txt", "**/missing.txt"] globTestExample2 none
      it "Root/foo/bar/baz.txt + Root/foo2/bar/qux2.md" do
        assertGlobManyResult !["Root/foo/bar/baz.txt", "Root/foo2/bar/qux2.md"]
          globTestExample2
          (some (tree! "Root" {
            "foo"  { "bar" { "baz.txt" } },
            "foo2" { "bar" { "qux2.md" } }
          }))

end GlobSpec
end
