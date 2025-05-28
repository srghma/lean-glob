import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Lean.Parser.Term

/- set_option diagnostics true -/

/-- A non-empty list structure -/
structure NonEmptyList (α : Type u) where
  /-- The underlying list -/
  val : List α
  /-- Proof that the list is non-empty -/
  property : val ≠ []
  deriving Hashable, Ord, Repr, DecidableEq --, BEq

universe u
variable {α : Type}

instance [BEq α] : BEq (NonEmptyList α) where
  beq a b := a.val == b.val

instance [ToString α] : ToString (NonEmptyList α) where
  toString a := toString a.val

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

@[inline] def toList (nel : NonEmptyList α) : List α := nel.val

@[inline] def head (nel : NonEmptyList α) : α :=
  match h_proof : nel.val with
  | firstElement :: _ => firstElement
  | [] => False.elim (nel.property h_proof)

@[inline] def tail (nel : NonEmptyList α) : List α :=
  match h : nel.val with
  | _ :: t => t
  | [] => False.elim (nel.property h)

@[inline] def cons (a : α) (nel : NonEmptyList α) : NonEmptyList α := ⟨a :: nel.val, List.cons_ne_nil a nel.val⟩

@[inline] def cons' (a : α) (l : List α) : NonEmptyList α := ⟨a :: l, List.cons_ne_nil a l⟩

@[inline] def singleton (a : α) : NonEmptyList α := ⟨[a], by simp⟩

@[inline] def mkNel (l : List α) (h : l ≠ []) : NonEmptyList α := ⟨l, h⟩

@[inline] def length (nel : NonEmptyList α) : Nat := nel.val.length

@[inline] def get (nel : NonEmptyList α) (i : Fin nel.length) : α := nel.val.get i

@[inline] def map {β : Type} (f : α → β) (nel : NonEmptyList α) : NonEmptyList β := ⟨nel.val.map f, by simp; exact nel.property⟩

@[inline] def append (nel1 nel2 : NonEmptyList α) : NonEmptyList α := ⟨nel1.val ++ nel2.val, by simp [nel1.property]⟩

end NonEmptyList

open Lean Macro Parser Term Elab Term

-- Helper function to create decidable proofs
-- private def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
--   let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
--   mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

-- TODO: use Lean.instToExprListOfToLevel instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (List α) ?
-- instance [ToExpr α] : ToExpr (NonEmptyList α) where
--   toTypeExpr := mkApp (mkConst ``NonEmptyList) (ToExpr.toTypeExpr α)
--   toExpr nel := mkApp2 (mkConst ``NonEmptyList.cons') (ToExpr.toExpr nel.head) (ToExpr.toExpr nel.tail)

-- instance [ToExpr α] : ToExpr (NonEmptyList α) where
--   toTypeExpr := mkApp (mkConst ``NonEmptyList) (ToExpr.toTypeExpr α)
--   toExpr nel :=
--     -- Deconstruct the underlying list value.
--     -- Since `nel.val` is guaranteed to be non-empty, it must be `x :: xs`.
--     match h_val : nel.val with
--     | x :: xs =>
--       -- Convert the head and tail to Lean expressions
--       let xExpr := ToExpr.toExpr x
--       let xsExpr := ToExpr.toExpr xs
--       -- Construct the proof term `List.cons_ne_nil x xs` directly
--       let proofExpr := mkApp2 (mkConst ``List.cons_ne_nil) xExpr xsExpr
--       -- Reconstruct the NonEmptyList using its fundamental constructor `NonEmptyList.mk`
--       -- The value `nel.val` is constructed using `List.cons` for the expression.
--       mkApp2 (mkConst ``NonEmptyList.mk) (mkApp2 (mkConst ``List.cons [levelOne]) xExpr xsExpr) proofExpr
--     | [] =>
--       -- This case is unreachable by `NonEmptyList.property`, but must be covered for exhaustiveness.
--       -- `False.elim (nel.property h_val)` creates a term of arbitrary type, allowing `toExpr` to proceed.
--       False.elim (nel.property h_val)

instance {α : Type u} [ToLevel.{u}] [ToExpr α] : ToExpr (NonEmptyList α) :=
  let type := toTypeExpr α
  let level := toLevel.{u}
  { toExpr := fun nel =>
      -- Extract the head and tail from the non-empty list
      match h : nel.val with
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
    -- match h_val : elems.getElems.toList with
    -- | x :: xs => ``(NonEmptyList.mkNel [$elems,*] (List.cons_ne_nil $x $xs))
    -- | [] => Macro.throwError "nel! literal must contain at least one element"
    let terms := elems.getElems
    if terms.isEmpty then
      Macro.throwError "nel! literal must contain at least one element"
    else
      ``(NonEmptyList.mkNel [$elems,*] (by simp))

-- Examples
example : NonEmptyList Nat := nel![1, 2, 3]
example : NonEmptyList String := nel!["hello", "world"]
example : NonEmptyList Nat := nel![10]

-- Test basic operations
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
