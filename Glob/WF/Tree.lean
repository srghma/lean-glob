import Glob.WF.Elab
import Glob.Data.Tree
import Aesop
open Tree

/--
Match a single pattern segment against a tree dir name.
- `lit s` matches if `s = name`.
- `oneStar` matches any single name.
- `doubleStar` is handled at pattern list level, not here.
-/
def PatternSegmentNonWF.match (seg : PatternSegmentNonWF) (name : String) : Bool :=
  match NonEmptyString.fromString? name with
  | none => false
  | some nes =>
    match seg with
    | .lit s => s == nes
    | .oneStar => true
    | .doubleStar => false

mutual
  def matchAux : List PatternSegmentNonWF → Tree → Option Tree
    | [], t => some (match t with
        | .file n => file n
        | .dir n _ => dir n [])
    | .doubleStar :: ps, t =>
      -- If no more patterns after **, return the full subtree
      (if ps = [] then some t else matchAux ps t) <|>
        match t with
        | .file _ => none
        | .dir name children =>
          match matchList (.doubleStar :: ps) children with
          | some cs => some (dir name cs)
          | none => none
    | seg :: ps, .file name =>
      if ps = [] ∧ seg.match name then
        some (file name)
      else
        none
    | seg :: ps, .dir name children =>
      if seg.match name then
        if ps = [] then
          some (dir name [])
        else
          match matchList ps children with
          | some cs => some (dir name cs)
          | none => none
      else
        none

  def matchList : List PatternSegmentNonWF → List Tree → Option (List Tree)
    | _, [] => none
    | ps, t :: ts =>
      match matchAux ps t with
      | some t' =>
        match matchList ps ts with
        | some ts' => some (t' :: ts')
        | none => some [t']
      | none =>
        matchList ps ts
end

def glob : (NonEmptyList PatternSegmentNonWF) -> Tree -> Option Tree
  | ⟨[], h⟩, t => by contradiction
  | ⟨ps, h⟩, t => matchAux ps t

def globMany (xss : NonEmptyList (NonEmptyList PatternSegmentNonWF)) (t : Tree) : Option Tree :=
  xss.toList.filterMap (fun ps => glob ps t) |> NonEmptyList.fromList? |>.map Tree.mergeAll1

#guard glob (patternNonWFStrict "Glob") (tree! "Glob" { "A" { } }) = some (tree! "Glob" {})
#guard glob (patternNonWFStrict "Glob/*") (tree! "Glob" { "A" { }, "B" { } }) = some (tree! "Glob" { "A" {}, "B" {} })
#guard glob (patternNonWFStrict "Glob/A") (tree! "Glob" { "A" { } }) = some (tree! "Glob" { "A" { } })
#guard glob (patternNonWFStrict "Glob/A") (tree! "Glob" { "A" }) = some (tree! "Glob" { "A" })
#guard glob (patternNonWFStrict "Glob/B") (tree! "Glob" { "A" { } }) = none

def globTestExample1 := tree! "Glob" { "A" { "X" { } }, "B" { "Y" { } } }

#guard glob (patternNonWFStrict "**") globTestExample1 = some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } })
#guard glob (patternNonWFStrict "**/X") globTestExample1 = some (tree! "Glob" { "A" { "X" {} } })
#guard glob (patternNonWFStrict "**/Y") globTestExample1 = some (tree! "Glob" { "B" { "Y" {} } })
#guard glob (patternNonWFStrict "**/Z") globTestExample1 = none
#guard glob (patternNonWFStrict "Glob/*") globTestExample1 = some (tree! "Glob" { "A" {}, "B" {} })
#guard glob (patternNonWFStrict "Glob/**") globTestExample1 = some globTestExample1
#guard glob (patternNonWFStrict "Glob/**") globTestExample1 = some globTestExample1
#guard glob (patternNonWFStrict "Glob/A/*") globTestExample1 = some (tree! "Glob" { "A" { "X" {} } })
#guard glob (patternNonWFStrict "Glob/A/**") globTestExample1 = some (tree! "Glob" { "A" { "X" { } } })
#guard glob (patternNonWFStrict "Glob/A/X") globTestExample1 = some (tree! "Glob" { "A" { "X" {} } })
#guard glob (patternNonWFStrict "Glob/B/**") globTestExample1 = some (tree! "Glob" { "B" { "Y" {} } })
#guard glob (patternNonWFStrict "Glob/C") globTestExample1 = none


def globTestExample2 := tree! "Root" {
  "foo" { "file.txt", "bar" { "baz.txt" , "qux.md" } },
  "foo2" { "file2.txt", "bar" { "baz2.txt", "qux2.md" }  },
  "alpha" { "beta" { "gamma" { "delta.txt"  } } },
  "zeta" {}
}

#guard glob (patternNonWFStrict "*") (tree! "foo" {}) = some (tree! "foo" {})
#guard glob (patternNonWFStrict "**") (tree! "root" {}) = some (tree! "root" {})
#guard glob (patternNonWFStrict "**/baz.txt") globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#guard glob (patternNonWFStrict "**/delta.txt") globTestExample2 = some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } })
#guard glob (patternNonWFStrict "**/file.txt") globTestExample2 = some (tree! "Root" { "foo" { "file.txt"  } })
#guard glob (patternNonWFStrict "**/qux.md") globTestExample2 = some (tree! "Root" { "foo" { "bar" { "qux.md" } } })
#guard glob (patternNonWFStrict "Root") globTestExample2 = some (tree! "Root" {})
#guard glob (patternNonWFStrict "Root/*") globTestExample2 = some (Tree.dir "Root" [Tree.dir "foo" [], Tree.dir "foo2" [], Tree.dir "alpha" [], Tree.dir "zeta" []])
#guard glob (patternNonWFStrict "Root/**") globTestExample2 = some globTestExample2
#guard glob (patternNonWFStrict "Root/**/bar/*") globTestExample2 = (some (tree! "Root" { "foo" { "bar" { "baz.txt", "qux.md" } }, "foo2" { "bar" { "baz2.txt", "qux2.md" } } }))
#guard glob (patternNonWFStrict "Root/**/delta.txt") globTestExample2 = some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } })
#guard glob (patternNonWFStrict "Root/**/file.txt") globTestExample2 = some (tree! "Root" { "foo" { "file.txt"  } })
#guard glob (patternNonWFStrict "Root/*/*/*/delta.txt") globTestExample2 = some (tree! "Root" { "alpha" { "beta" { "gamma" { "delta.txt"  } } } })
#guard glob (patternNonWFStrict "Root/foo/**/baz.txt") globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#guard glob (patternNonWFStrict "Root/foo/*/baz.txt") globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#guard glob (patternNonWFStrict "Root/foo/*/doesntexist.txt") globTestExample2 = none
#guard glob (patternNonWFStrict "Root/foo/bar/baz.txt") globTestExample2 = some (tree! "Root" { "foo" { "bar" { "baz.txt"  } } })
#guard glob (patternNonWFStrict "Root/foo/bar/baz.txt/extra") globTestExample2 = none
#guard glob (patternNonWFStrict "Root/foo/bar/notfound.txt") globTestExample2 = none


#guard globMany (nel![patternNonWFStrict "Glob/A", patternNonWFStrict "Glob/B"]) (tree! "Glob" { "A" {}, "B" {} }) = some (tree! "Glob" { "A" {}, "B" {} })

#guard globMany (nel![patternNonWFStrict "Glob/A", patternNonWFStrict "Glob/C"]) (tree! "Glob" { "A" {}, "B" {} })
  = some (tree! "Glob" { "A" {} })

#guard globMany (nel![patternNonWFStrict "**/X", patternNonWFStrict "**/Y"]) globTestExample1
  = some (tree! "Glob" { "A" { "X" {} }, "B" { "Y" {} } })

#guard globMany (nel![patternNonWFStrict "**/baz.txt", patternNonWFStrict "**/delta.txt"]) globTestExample2
  = some (tree! "Root" {
    "foo"   { "bar" { "baz.txt" } },
    "alpha" { "beta" { "gamma" { "delta.txt" } } }
  })

#guard globMany (nel![patternNonWFStrict "**/file.txt", patternNonWFStrict "**/qux.md"]) globTestExample2 = some (tree! "Root" { "foo" { "file.txt", "bar" { "qux.md" } } })

#guard globMany (nel![patternNonWFStrict "**/doesntexist.txt", patternNonWFStrict "**/missing.txt"]) globTestExample2 = none

#guard globMany (nel![patternNonWFStrict "Root/foo/bar/baz.txt", patternNonWFStrict "Root/foo2/bar/qux2.md"]) globTestExample2
  = some (tree! "Root" {
    "foo"  { "bar" { "baz.txt" } },
    "foo2" { "bar" { "qux2.md" } }
  })
