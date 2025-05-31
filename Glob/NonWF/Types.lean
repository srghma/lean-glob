import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.Data.NonEmptyString
import Glob.Data.NonEmptyList
import Glob.Utils.NEFromTo

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

inductive PatternSegmentNonWF where
  | doubleStar : PatternSegmentNonWF
  | oneStar : PatternSegmentNonWF
  | lit : NonEmptyString -> PatternSegmentNonWF
  deriving Inhabited, Repr, BEq, Ord, Hashable, DecidableEq

instance : Coe NonEmptyString PatternSegmentNonWF where
  coe a := .lit a

open Lean Meta Elab

instance : ToExpr PatternSegmentNonWF where
  toTypeExpr := mkConst ``PatternSegmentNonWF
  toExpr
    | .lit nes => mkApp (mkConst ``PatternSegmentNonWF.lit) (toExpr nes)
    | .oneStar => mkConst ``PatternSegmentNonWF.oneStar
    | .doubleStar => mkConst ``PatternSegmentNonWF.doubleStar

def PatternSegmentNonWF.toString : PatternSegmentNonWF → String
| .doubleStar => "**"
| .oneStar => "*"
| .lit s => NonEmptyString.toString s

instance : ToString PatternSegmentNonWF where
  toString := PatternSegmentNonWF.toString

def PatternSegmentNonWF.fromNES (nes : NonEmptyString) : PatternSegmentNonWF :=
  match nes.toString with
  | "**" => .doubleStar
  | "*"  => .oneStar
  | _    => .lit nes

/--
Match a single pattern segment against a tree dir name.
- `lit s` matches if `s = name`.
- `oneStar` matches any single name.
- `doubleStar` is handled at pattern list level, not here.
-/
def PatternSegmentNonWF.matchNES (seg : PatternSegmentNonWF) (name : NonEmptyString) : Bool :=
  match seg with
  | .lit s => s == name
  | .oneStar => true
  | .doubleStar => false

def PatternSegmentNonWF.matchS (seg : PatternSegmentNonWF) (name : String) : Bool :=
  match NonEmptyString.fromString? name with
  | none => false
  | some name' => PatternSegmentNonWF.matchNES seg name'

open Lean Meta

-- set_option diagnostics true

instance : ToExpr PatternSegmentNonWF where
  toTypeExpr := mkConst ``PatternSegmentNonWF
  toExpr
  | .doubleStar => mkConst ``PatternSegmentNonWF.doubleStar
  | .oneStar    => mkConst ``PatternSegmentNonWF.oneStar
  | .lit s      => mkApp (mkConst ``PatternSegmentNonWF.lit) (toExpr s)

abbrev PatternNonWF' := List PatternSegmentNonWF
abbrev PatternNonWF := NonEmptyList PatternSegmentNonWF

def PatternNonWF'.toString (ps : PatternNonWF') : String := String.intercalate "/" (ps.map PatternSegmentNonWF.toString)

-- "" ok
-- "/" not ok
def PatternNonWF'.fromStringStrict (s : String) : Option PatternNonWF' :=
  if s == "" then some [] -- empty pattern, OK
  else
    s.split (· == '/')
    |> ToNE.Traverse.«LS->LNES»
    |>.map (·.map PatternSegmentNonWF.fromNES)

def PatternNonWF'.fromStringLax (s : String) : PatternNonWF' :=
  s.split (· == '/')
  |> ToNE.FilterMap.«LS->LNES»
  |>.map PatternSegmentNonWF.fromNES

def PatternNonWF.toString : PatternNonWF -> String := (PatternNonWF'.toString ·.toList)
def PatternNonWF.fromStringStrict : String -> Option PatternNonWF := (PatternNonWF'.fromStringStrict · >>= NonEmptyList.fromList?)

elab "patternNonWFLax" pat:str : term => return Lean.toExpr (PatternNonWF'.fromStringLax pat.getString)

elab "patternNonWFStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF.fromStringStrict s with
  | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
  | none => throwError s!"invalid non-well-formed pattern: {s}"

#guard nel![PatternSegmentNonWF.oneStar] = nel![PatternSegmentNonWF.oneStar]
#guard PatternNonWF.fromStringStrict "*" = .some nel![PatternSegmentNonWF.oneStar]
#guard patternNonWFLax "*" = [PatternSegmentNonWF.oneStar]
#guard patternNonWFStrict "*" = nel![PatternSegmentNonWF.oneStar]
