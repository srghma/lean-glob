import Lean

open Lean Elab Term Meta

syntax posixPathNamedArg := "(" ident ":=" term ")"
syntax "posixPathTest! " posixPathNamedArg* str : term

elab_rules : term
| `(posixPathTest! $[( $ids:ident := $terms:term )]* $s:str) => do
  let mut apStx? : Option Term := none
  let mut acStx? : Option Term := none
  for id in ids, t in terms do
    if id.getId == `allowParents then apStx? := some t
    else if id.getId == `allowCwd then acStx? := some t
    else throwErrorAt id "unknown argument"
  let str := s.getString
  let resStx := Syntax.mkStrLit s!"{str} - {apStx?.isSome} - {acStx?.isSome}"
  elabTerm resStx none

#eval posixPathTest! "foo"
#eval posixPathTest! (allowParents := true) "foo"
#eval posixPathTest! (allowCwd := false) "foo"
#eval posixPathTest! (allowParents := true) (allowCwd := false) "foo"
#eval posixPathTest! (allowCwd := false) (allowParents := true) "foo"

