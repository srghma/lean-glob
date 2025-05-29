import Lean
import Init.Data.Format.Basic
import Glob.Data.NonEmptyList
open Lean
open Lean.Parser

open List

inductive Tree
| file (name : String) : Tree
| dir (name : String) (children : List Tree) : Tree
deriving Inhabited, BEq --, Repr

def Tree.toString : Tree → String
  | Tree.file name => "\"" ++ name ++ "\""
  | Tree.dir name [] => "\"" ++ name ++ "\" {}"
  | Tree.dir name children =>
    let childrenStr := String.intercalate ", " (children.map Tree.toString)
    "\"" ++ name ++ "\" { " ++ childrenStr ++ " }"

def Tree.toStringMacro (t : Tree) : String := "tree! " ++ Tree.toString t

open Std.Format in
partial def Tree.toFormat : Tree → Format
| Tree.file name =>
  -- Just the filename in quotes, e.g. `"foo"`
  text "\"" ++ text name ++ text "\""
| Tree.dir name children =>
  let childrenFmt :=
    if children.isEmpty then
      .nil
    else
      -- Join children with commas and line breaks, nested for indentation
      nest 2 <|
        line ++
        group (
          join (children.map (fun c => c.toFormat) |>.intersperse (text "," ++ line))
        ) ++
        line
  group (
    text "tree! " ++
    text "\"" ++ text name ++ text "\"" ++
    text " {" ++
    childrenFmt ++
    text "}"
  )

instance : Repr Tree where
  reprPrec t _ := f!"{t.toFormat}"

instance : ToString Tree where
  toString := Tree.toStringMacro

mutual
  def decEqTree : (a b : Tree) → Decidable (a = b)
  | Tree.file a, Tree.file b =>
    match decEq a b with
    | isTrue h  => isTrue (by rw [h])
    | isFalse h => isFalse (by simp [h])
  | Tree.dir a as, Tree.dir b bs =>
    match decEq a b, decEqListTree as bs with
    | isTrue ha, isTrue hb => isTrue (by rw [ha, hb])
    | isFalse ha, _        => isFalse (by intro h; injection h with ha' _; exact ha ha')
    | _, isFalse hb        => isFalse (by intro h; injection h with _ hb'; exact hb hb')
  | Tree.dir a as, Tree.file b => isFalse (by intro h; simp_all only [reduceCtorEq])
  | Tree.file a, Tree.dir b bs => isFalse (by intro h; simp_all only [reduceCtorEq])

  def decEqListTree : (a b : List Tree) → Decidable (a = b)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (by intro h; cases h)
  | _ :: _, [] => isFalse (by intro h; cases h)
  | x :: xs, y :: ys =>
    match decEqTree x y, decEqListTree xs ys with
    | isTrue hx, isTrue hxs => isTrue (by rw [hx, hxs])
    | isFalse hx, _         => isFalse (by intro h; injection h with hx' _; exact hx hx')
    | _, isFalse hxs        => isFalse (by intro h; injection h with _ hxs'; exact hxs hxs')
end

instance : DecidableEq Tree := decEqTree

declare_syntax_cat treeElem
syntax str : treeElem
syntax str "{" treeElem,* "}" : treeElem
declare_syntax_cat treeElems
syntax treeElem,* : treeElems
syntax "tree!" treeElem : term
syntax "tree!" "{" treeElems "}" : term

-- tree! "RootDir" { "Foo" {...}, "Bar" }
macro_rules
| `(tree! $name:str) => `(Tree.file $(Lean.Syntax.mkStrLit name.getString))
| `(tree! $name:str { $children:treeElem,* }) => do
    let childTerms ← children.getElems.mapM fun c => `(tree! $c)
    `(Tree.dir $(Lean.Syntax.mkStrLit name.getString) [$childTerms,*])

-- tree! { "Foo" {...}, "Bar" }
macro_rules
| `(tree! { $elems:treeElem,* }) => do
    let elemTerms ← elems.getElems.mapM fun e => `(tree! $e)
    `([$elemTerms,*])

#guard tree! "Glob" { "NonWF" { } } = Tree.dir "Glob" [Tree.dir "NonWF" []]
#guard tree! "Glob" { "NonWF" { "a" } } = Tree.dir "Glob" [Tree.dir "NonWF" [.file "a"]]
#guard tree! "Glob" { "NonWF" { "a", "b" } } = Tree.dir "Glob" [Tree.dir "NonWF" [.file "a", .file "b"]]
#guard tree! "Glob" { "NonWF" { "a", "b" {} } } = Tree.dir "Glob" [Tree.dir "NonWF" [.file "a", .dir "b" []]]
#guard tree! { "NonWF" { } } = [Tree.dir "NonWF" []]

-----------------

mutual
  def Tree.merge : Tree → Tree → Tree
    | .file n, .file _ => .file n
    | .file n, .dir _ _ => .file n
    | .dir _ _, .file n => .file n
    | .dir n1 cs1, .dir n2 cs2 =>
      if n1 == n2 then
        .dir n1 (mergeChildren cs1 cs2)
      else
        .dir n1 cs1  -- Keep first if names differ

  def Tree.mergeChildren : List Tree → List Tree → List Tree
    | xs, [] => xs
    | xs, y :: ys =>
      let (matched, rest) := xs.partition (fun x =>
        match x, y with
        | .file n1, .file n2 => n1 == n2
        | .file n1, .dir n2 _ => n1 == n2
        | .dir n1 _, .file n2 => n1 == n2
        | .dir n1 _, .dir n2 _ => n1 == n2
      )
      let merged :=
        match matched with
        | [] => [y]
        | x :: _ => [Tree.merge x y]
      mergeChildren (rest ++ merged) ys
end

def Tree.mergeAll1 (rs : NonEmptyList Tree) : Tree :=
  match rs with
  | ⟨[], h⟩ => by contradiction
  | ⟨x :: xs, h⟩  => xs.foldl Tree.merge x

-- .file + .file (same name): keep first
#guard Tree.merge (.file "A") (.file "A") == .file "A"

-- .file + .dir: keep .file
#guard Tree.merge (.file "A") (.dir "A" []) == .file "A"
#guard Tree.merge (.dir "A" []) (.file "A") == .file "A"

-- .dir + .dir, same name: merge children
#guard Tree.merge (.dir "X" [.file "A"]) (.dir "X" [.file "B"])
  == .dir "X" [.file "A", .file "B"]

-- .dir + .dir, different name: keep first
#guard Tree.merge (.dir "X" [.file "A"]) (.dir "Y" [.file "B"])
  == .dir "X" [.file "A"]

-- Deep merge: .file wins over .dir, even nested
#guard Tree.merge (.file "deep") (.dir "deep" [.file "sub"]) == .file "deep"
#guard Tree.merge (.dir "deep" [.file "sub"]) (.file "deep") == .file "deep"
