import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.Utils.NonEmptyString
import Glob.Utils.NonEmptyList
import Glob.Utils.NEFromTo
-- import Mathlib.Data.List.Induction
-- import Aesop
-- import LeanCopilot

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)


--------------------------
inductive PatternSegmentNonWF where
  | doubleStar : PatternSegmentNonWF
  | oneStar : PatternSegmentNonWF
  | lit : NonEmptyString -> PatternSegmentNonWF
  deriving Inhabited, Repr, BEq, Ord, Hashable, DecidableEq

instance : Coe NonEmptyString PatternSegmentNonWF where
  coe a := .lit a

def PatternSegmentNonWF.toString : PatternSegmentNonWF → String
| .doubleStar => "**"
| .oneStar => "*"
| .lit s => NonEmptyString.toString s

instance : ToString PatternSegmentNonWF where
  toString := PatternSegmentNonWF.toString

def PatternSegmentNonWF.fromNES (nes : NonEmptyString) : PatternSegmentNonWF :=
  match nes.val with
  | "**" => .doubleStar
  | "*"  => .oneStar
  | _    => .lit nes

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
def PatternNonWF'.fromStringStrict (s : String) : Option PatternNonWF' := (ToNE.Traverse.«LS->LNES» (s.split (· == '/'))).map (·.map PatternSegmentNonWF.fromNES)

def PatternNonWF'.fromStringLax (s : String) : PatternNonWF' := (ToNE.FilterMap.«LS->LNES» (s.split (· == '/'))).map (PatternSegmentNonWF.fromNES)


def PatternNonWF.toString (ps : PatternNonWF) : String := PatternNonWF'.toString ps.toList
def PatternNonWF.fromStringStrict (s : String) : Option PatternNonWF := PatternNonWF'.fromStringStrict s >>= NonEmptyList.fromList?

set_option diagnostics.threshold 50

elab "patternNonWFLax" pat:str : term => do
  let s := pat.getString
  return (Lean.toExpr (PatternNonWF'.fromStringLax s))

elab "patternNonWFStrict" pat:str : term => do
  let s := pat.getString
  match PatternNonWF.fromStringStrict s with
  | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
  | none   => throwError s!"invalid non-well-formed pattern: {s}"

#guard nel![PatternSegmentNonWF.oneStar] = nel![PatternSegmentNonWF.oneStar]
#guard PatternNonWF.fromStringStrict "*" = .some nel![PatternSegmentNonWF.oneStar]
#guard patternNonWFLax "*" = [PatternSegmentNonWF.oneStar]
#guard patternNonWFStrict "*" = nel![PatternSegmentNonWF.oneStar]
