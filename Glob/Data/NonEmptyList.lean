import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Lean.Parser.Term
import Batteries.Data.List.Basic

structure NonEmptyList (α : Type u) where
  toList : List α
  property : toList ≠ []
  deriving Hashable, Ord, Repr, DecidableEq

universe u
variable {α : Type}

instance [BEq α] : BEq (NonEmptyList α) where
  beq a b := a.toList == b.toList

instance [ToString α] : ToString (NonEmptyList α) where
  toString a := toString a.toList

instance [Inhabited α] : Inhabited (NonEmptyList α) where
  default := ⟨[default], List.cons_ne_nil default []⟩

-- ToExpr instance for compile-time evaluation
open Lean Elab Term Meta

namespace NonEmptyList

@[inline] def fromList? (l : List α) : Option (NonEmptyList α) :=
  match h_l_struct : l with
  | [] => none
  | _ :: _ => some ⟨l, by simp [h_l_struct]⟩

@[inline] def fromList! [Inhabited α] (l : List α) : NonEmptyList α :=
  match NonEmptyList.fromList? l with
  | some nel => nel
  | none => panic! "Expected non-empty list"

@[inline] def head (nel : NonEmptyList α) : α :=
  match h_proof : nel.toList with
  | firstElement :: _ => firstElement
  | [] => False.elim (nel.property h_proof)

@[inline] def tail (nel : NonEmptyList α) : List α :=
  match h : nel.toList with
  | _ :: t => t
  | [] => False.elim (nel.property h)

@[inline] def cons (a : α) (nel : NonEmptyList α) : NonEmptyList α := ⟨a :: nel.toList, List.cons_ne_nil a nel.toList⟩

@[inline] def cons' (a : α) (l : List α) : NonEmptyList α := ⟨a :: l, List.cons_ne_nil a l⟩

@[inline] def singleton (a : α) : NonEmptyList α := ⟨[a], by simp⟩

@[inline] def length (nel : NonEmptyList α) : Nat := nel.toList.length

@[inline] def get (nel : NonEmptyList α) (i : Fin nel.length) : α := nel.toList.get i

@[inline] def map {β : Type} (f : α → β) (nel : NonEmptyList α) : NonEmptyList β := ⟨nel.toList.map f, by simp; exact nel.property⟩

@[inline] def append (nel1 nel2 : NonEmptyList α) : NonEmptyList α := ⟨nel1.toList ++ nel2.toList, by simp [nel1.property]⟩

-- needs batteries
@[inline] def inits [Inhabited α] (nel : NonEmptyList α) : NonEmptyList (NonEmptyList α) :=
  let allInits := nel.toList.inits.drop 1  -- drop the initial empty list
  fromList! (allInits.map fromList!)

end NonEmptyList

open Lean Macro Parser Term Elab Term

instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmptyList α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun nel =>
      match h : nel.toList with
      | x :: xs =>
        let xExpr := toExpr x
        let xsExpr := toExpr xs
        let listExpr := mkApp3 (mkConst ``List.cons [level]) type xExpr xsExpr
        let proofExpr := mkApp3 (mkConst ``List.cons_ne_nil [level]) type xExpr xsExpr
        mkApp3 (mkConst ``NonEmptyList.mk [level]) type listExpr proofExpr
      | [] => False.elim (nel.property h),
    toTypeExpr := mkApp (mkConst ``NonEmptyList [level]) type }

-- Macro for creating non-empty list literals
syntax "nel![" withoutPosition(term,*,?) "]" : term

macro_rules
  | `(nel![ $elems,* ]) => do
    let terms := elems.getElems
    if terms.isEmpty then
      Macro.throwError "nel! literal must contain at least one element"
    else
      ``(NonEmptyList.mk [$elems,*] (by simp))

example : NonEmptyList Nat := nel![1, 2, 3]
example : NonEmptyList String := nel!["hello", "world"]
example : NonEmptyList Nat := nel![10]

#guard (nel![1, 2, 3]).head = 1 -- Should output 1
#guard (nel![1, 2, 3]).tail = [2, 3] -- Should output [2, 3]
#guard (nel![1, 2, 3]).length = 3 -- Should output 3

-- #eval (toExpr $ nel![1]) -- Should output 1

-- Elaborator-based version for compile-time evaluation
-- elab "nel_elab!" "[" elems:term,* "]" : term => do
--   let termArray := elems.getElems.toList
--   if termArray.isEmpty then
--     throwError "nel_elab! literal must contain at least one element"
--   else
--     -- Create a list from the elements
--     let listExpr ← `([$elems,*])
--     let listTerm ← elabTerm listExpr none

--     -- Create a more robust proof using decidability
--     let proofTerm ← `(by simp)
--     let proof ← elabTerm proofTerm none

--     -- Construct the NonEmptyList.mk expression
--     let result := mkApp2 (mkConst ``NonEmptyList.mkNel) listTerm proof
--     return result


-- -- Test the elaborator version
-- example : NonEmptyList Nat := nel_elab![1, 2, 3]
-- example : NonEmptyList String := nel_elab!["hello", "world"]
-- example : NonEmptyList Nat := nel_elab![10]

-- #eval nel_elab![10]
