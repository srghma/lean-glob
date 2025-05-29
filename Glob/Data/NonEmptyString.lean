import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Lean.Parser.Term
import Lean

/-
A non-empty string type for better type safety
-/
structure NonEmptyString where
  toString : String
  property : toString ≠ ""
  deriving BEq, Hashable, Ord, Repr, DecidableEq

instance : ToString NonEmptyString where
  toString s := s.toString

instance : Inhabited NonEmptyString where
  default := ⟨"default", by simp⟩

open Lean Meta Elab

private def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  -- Eq.refl.{1} is used because we're dealing with Type 0 (not Prop)
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

instance : ToExpr NonEmptyString where
  toTypeExpr := mkConst ``NonEmptyString
  toExpr nes :=
    let sVal := nes.toString
    let sExpr := toExpr sVal      -- `Expr` for the string literal, e.g., `"world"`
    let emptyStrExpr := toExpr "" -- `Expr` for `""`

    -- 1. The underlying equality proposition: `sVal = ""`
    --    `Eq.{1} String sExpr emptyStrExpr` (universe level 1 for Type 0)
    let propIsEqEmpty := mkApp3 (mkConst ``Eq [1]) (mkConst ``String) sExpr emptyStrExpr

    -- 2. The `Decidable` instance for `sVal = ""`
    --    `instDecidableEqString sExpr emptyStrExpr`
    let instDecEqEmptyExpr := mkApp2 (mkConst ``instDecidableEqString) sExpr emptyStrExpr

    -- 3. The non-equality proposition: `sVal ≠ ""`, which is `¬ (sVal = "")`
    --    `Not propIsEqEmpty`
    let propIsNonEmpty := mkApp (mkConst ``Not) propIsEqEmpty

    -- 4. The `Decidable` instance for `sVal ≠ ""`
    --    `instDecidableNot propIsEqEmpty instDecEqEmptyExpr`
    let instDecNeEmptyExpr := mkApp2 (mkConst ``instDecidableNot) propIsEqEmpty instDecEqEmptyExpr

    -- 5. The final proof term `of_decide_eq_true ...`
    --    Using our helper `mkDecidableProof`
    let finalProofExpr := mkDecidableProof propIsNonEmpty instDecNeEmptyExpr

    -- Construct the final `NonEmptyString.mk` expression
    mkApp2 (mkConst ``NonEmptyString.mk) sExpr finalProofExpr

namespace NonEmptyString

@[inline] def fromString? (s : String) : Option NonEmptyString := if h : s ≠ "" then some ⟨s, h⟩ else none

@[inline] def fromString! (s : String) : NonEmptyString :=
  match NonEmptyString.fromString? s with
  | some nes => nes
  | none => panic! "Expected non-empty string, got: '{s}'"

@[inline] def fromNELChar (cs : List Char) (h : cs ≠ []) : NonEmptyString :=
  ⟨⟨cs⟩, by
    intro contra
    apply h
    rw [String.ext_iff] at contra
    exact contra⟩

@[inline] def fromLChar? (cs : List Char) : Option NonEmptyString := fromString? (String.mk cs)

@[inline] def fromLChar! (cs : List Char) : NonEmptyString :=
  match NonEmptyString.fromLChar? cs with
  | some nes => nes
  | none => panic! "Expected non-empty string, got: '{cs}'"

end NonEmptyString

instance : ToString NonEmptyString where
  toString := NonEmptyString.toString

open Lean Macro

macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (of_decide_eq_true (Eq.refl true)) : NonEmptyString) )

elab "nes_elab!" s:str : term => do
  let strVal := s.getString
  match NonEmptyString.fromString? strVal with
  | some nesVal => return (toExpr nesVal)
  | none => throwErrorAt s "String literal cannot be empty for nes!"

example := nes!"world"
example := nes_elab!"world"

#guard (nes!"hello" = nes_elab!"hello")
