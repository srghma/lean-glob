module
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
public import Glob.WF.Elab
public import Tree
public meta import Tree
public import Lean.Elab.Command

@[expose] public section

open Tree NonEmpty.String NonEmpty.List

namespace Glob

mutual
  def globList : List PatternSegmentNonWF → Tree → Option Tree
    | [], t => some (match t with
        | .file n => file n
        | .dir n _ => dir n [])
    | .doubleStar :: ps, t =>
      -- If no more patterns after **, return the full subtree
      (if ps = [] then some t else globList ps t) <|>
        match t with
        | .file _ => none
        | .dir name children =>
          match globListListTree (.doubleStar :: ps) children with
          | some cs => some (dir name cs)
          | none => none
    | seg :: ps, .file name =>
      if ps = [] ∧ seg.matchS name then
        some (file name)
      else
        none
    | seg :: ps, .dir name children =>
      if seg.matchS name then
        if ps = [] then
          some (dir name [])
        else
          match globListListTree ps children with
          | some cs => some (dir name cs)
          | none => none
      else
        none

  def globListListTree : List PatternSegmentNonWF → List Tree → Option (List Tree)
    | _, [] => none
    | ps, t :: ts =>
      match globList ps t with
      | some t' =>
        match globListListTree ps ts with
        | some ts' => some (t' :: ts')
        | none => some [t']
      | none => globListListTree ps ts
end

class TreeGlobForPattern (α : Type) where
  glob : α → Tree → Option Tree
  globMany : NonEmptyList α → Tree → Option Tree

protected def globManyList (xss : NonEmptyList (List PatternSegmentNonWF)) (t : Tree) : Option Tree :=
  xss.toList.filterMap (globList · t)
  |> NonEmptyList.fromList?
  |>.map Tree.mergeAll1

instance : TreeGlobForPattern (List PatternSegmentNonWF) where
  glob := globList
  globMany := Glob.globManyList

protected def globNEL (ps : NonEmptyList PatternSegmentNonWF) (t : Tree) : Option Tree :=
  match ps with
  | ⟨[], _⟩ => by contradiction
  | ⟨ps, h⟩ => globList ps t

protected def globManyNEL (xss : NonEmptyList (NonEmptyList PatternSegmentNonWF)) (t : Tree) : Option Tree :=
  xss.toList.filterMap (Glob.globNEL · t)
  |> NonEmptyList.fromList?
  |>.map Tree.mergeAll1

instance : TreeGlobForPattern (NonEmptyList PatternSegmentNonWF) where
  glob := Glob.globNEL
  globMany := Glob.globManyNEL

def globValidated (pv : PatternValidated) (t : Tree) : Option Tree :=
  NonEmptyList.fromList? pv.pattern >>= (Glob.globNEL · t)

def globManyValidated (pvs : NonEmptyList PatternValidated) (t : Tree) : Option Tree
  := pvs.toList.filterMap (globValidated · t)
  |> NonEmptyList.fromList?
  |>.map Tree.mergeAll1

instance : TreeGlobForPattern PatternValidated where
  glob := Glob.globValidated
  globMany := Glob.globManyValidated

end Glob

namespace Tests

open Glob Glob.TreeGlobForPattern

open Lean Elab Command Meta

syntax "#testGlob" str term:arg " = " term : command
macro_rules
| `(#testGlob $a $b = $c) => do
  `(#guard glob (patternStrict $a) $b = $c
    #guard glob (patternNonWFStrict $a) $b = $c)

#testGlob "*" (tree! "Glob" { "A" { } }) = some (tree! "Glob" { })
#testGlob "**" (tree! "Glob" { "A" { } }) = some (tree! "Glob" { "A" { } })
#testGlob "Glob" (tree! "Glob" { "A" { } }) = some (tree! "Glob" { })
#testGlob "Glob/A" (tree! "Glob" { "A" { } }) = some (tree! "Glob" { "A" { } })
#testGlob "Glob/A" (tree! "Glob" { "A" }) = some (tree! "Glob" { "A" })
-- #testGlob "Glob/A/" (tree! "Glob" { "A" { } }) = some (tree! "Glob" { "A" { } })
-- #testGlob "Glob/A/" (tree! "Glob" { "A" }) = none
#testGlob "Glob/B" (tree! "Glob" { "A" { } }) = none
#testGlob "Glob/B" (tree! "Glob" { "A" }) = none

def globTestExample1 := tree! "Glob" { "A" { "X" { } }, "B" { "Y" { } } }

#testGlob "**" globTestExample1 = some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } })
#testGlob "**/X" globTestExample1 = some (tree! "Glob" { "A" { "X" {} } })
#testGlob "**/Y" globTestExample1 = some (tree! "Glob" { "B" { "Y" {} } })
#testGlob "**/Z" globTestExample1 = none
#testGlob "Glob/*" globTestExample1 = some (tree! "Glob" { "A" {}, "B" {} })
#testGlob "Glob/**" globTestExample1 = some globTestExample1
#testGlob "Glob/**" globTestExample1 = some globTestExample1
#testGlob "Glob/A/*" globTestExample1 = some (tree! "Glob" { "A" { "X" {} } })
#testGlob "Glob/A/**" globTestExample1 = some (tree! "Glob" { "A" { "X" { } } })
#testGlob "Glob/A/X" globTestExample1 = some (tree! "Glob" { "A" { "X" {} } })
#testGlob "Glob/B/**" globTestExample1 = some (tree! "Glob" { "B" { "Y" {} } })
#testGlob "Glob/C" globTestExample1 = none

def globTestExample2 := tree! "Root" {
  "foo" { "file.txt", "bar" { "baz.txt" , "qux.md" } },
  "foo2" { "file2.txt", "bar" { "baz2.txt", "qux2.md" }  },
  "alpha" { "beta" { "gamma" { "delta.txt"  } } },
  "zeta" {}
}

#testGlob "*" (tree! "foo" {}) = some (tree! "foo" {})
#testGlob "**" (tree! "root" {}) = some (tree! "root" {})
#testGlob "**/baz.txt" globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#testGlob "**/delta.txt" globTestExample2 = some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } })
#testGlob "**/file.txt" globTestExample2 = some (tree! "Root" { "foo" { "file.txt"  } })
#testGlob "**/qux.md" globTestExample2 = some (tree! "Root" { "foo" { "bar" { "qux.md" } } })
#testGlob "Root" globTestExample2 = some (tree! "Root" {})
#testGlob "Root/*" globTestExample2 = some (Tree.dir "Root" [Tree.dir "foo" [], Tree.dir "foo2" [], Tree.dir "alpha" [], Tree.dir "zeta" []])
#testGlob "Root/**" globTestExample2 = some globTestExample2
#testGlob "Root/**/bar/*" globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt", "qux.md" } }, "foo2" { "bar" { "baz2.txt", "qux2.md" } } })
#testGlob "Root/**/delta.txt" globTestExample2 = some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } })
#testGlob "Root/**/file.txt" globTestExample2 = some (tree! "Root" { "foo" { "file.txt"  } })
#testGlob "Root/*/*/*/delta.txt" globTestExample2 = some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } })
#testGlob "Root/foo/**/baz.txt" globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#testGlob "Root/foo/*/baz.txt" globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#testGlob "Root/foo/*/doesntexist.txt" globTestExample2 = none
#testGlob "Root/foo/bar/baz.txt" globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#testGlob "Root/foo/bar/baz.txt/extra" globTestExample2 = none
#testGlob "Root/foo/bar/notfound.txt" globTestExample2 = none

#guard globMany ![patternStrict "Glob/A", patternStrict "Glob/B"] (tree! "Glob" { "A" {}, "B" {} }) = some (tree! "Glob" { "A" {}, "B" {} })
#guard globMany ![patternStrict "Glob/A", patternStrict "Glob/B"] (tree! "Glob" { "A" {}, "B" {} }) = some (tree! "Glob" { "A" {}, "B" {} })

#guard globMany ![patternStrict "Glob/A", patternStrict "Glob/C"] (tree! "Glob" { "A" {}, "B" {} })
  = some (tree! "Glob" { "A" {} })

#guard globMany ![patternStrict "**/X", patternStrict "**/Y"] globTestExample1
  = some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } })

#guard globMany ![patternStrict "**/baz.txt", patternStrict "**/delta.txt"] globTestExample2
  = some (tree! "Root" {
    "foo"   { "bar" { "baz.txt" } },
    "alpha" { "beta" { "gamma" { "delta.txt" } } }
  })

#guard globMany ![patternStrict "**/file.txt", patternStrict "**/qux.md"] globTestExample2 = some (tree! "Root" { "foo" { "file.txt", "bar" { "qux.md" } } })

#guard globMany ![patternStrict "**/doesntexist.txt", patternStrict "**/missing.txt"] globTestExample2 = none

#guard globMany ![patternStrict "Root/foo/bar/baz.txt", patternStrict "Root/foo2/bar/qux2.md"] globTestExample2
  = some (tree! "Root" {
    "foo"  { "bar" { "baz.txt" } },
    "foo2" { "bar" { "qux2.md" } }
  })

#guard globMany ![patternStrict "Root/foo/bar/baz.txt", patternStrict "Root/foo2/bar/qux2.md"] globTestExample2
  = some (tree! "Root" {
    "foo"  { "bar" { "baz.txt" } },
    "foo2" { "bar" { "qux2.md" } }
  })

end Tests
end
