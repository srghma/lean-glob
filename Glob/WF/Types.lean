import Lean
import Lean.Elab.Term
import Lean.Parser.Term
import Glob.Data.NonEmptyString
import Glob.Data.NonEmptyList
import Glob.NonWF.Types
import Glob.NonWF.Normalize

--------------------------------------

-- Well-formedness rules as predicates
def canFollow : PatternSegmentNonWF → PatternSegmentNonWF → Prop
  | _, .lit _ => True
  | .lit _, .oneStar => True
  | .lit _, .doubleStar => True
  | .doubleStar, .doubleStar => False
  | .doubleStar, .oneStar => False
  | .oneStar, .doubleStar => True
  | .oneStar, .oneStar => True

def isValidSequence : List PatternSegmentNonWF → Prop
  | [] => False
  | [_] => True
  | prev :: next :: rest => canFollow prev next ∧ isValidSequence (next :: rest)

def canFollowDecidable (prev next : PatternSegmentNonWF) : Decidable (canFollow prev next) :=
  match prev, next with
  | _, .lit _ => isTrue (by simp [canFollow])
  | .lit _, .oneStar => isTrue (by simp [canFollow])
  | .lit _, .doubleStar => isTrue (by simp [canFollow])
  | .doubleStar, .doubleStar => isFalse (by simp [canFollow])
  | .doubleStar, .oneStar => isFalse (by simp [canFollow])
  | .oneStar, .doubleStar => isTrue (by simp [canFollow])
  | .oneStar, .oneStar => isTrue (by simp [canFollow])

instance isValidSequenceDecidable : (segments : List PatternSegmentNonWF) → Decidable (isValidSequence segments)
  | [] => isFalse (by simp [isValidSequence])
  | [_] => isTrue trivial
  | prev :: next :: rest =>
    match canFollowDecidable prev next, isValidSequenceDecidable (next :: rest) with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h, _ => isFalse (by intro ⟨h', _⟩; exact h h')
    | _, isFalse h => isFalse (by intro ⟨_, h'⟩; exact h h')

--------------------------------------

structure PatternValidated : Type where
  pattern : List PatternSegmentNonWF
  valid_sequence : isValidSequence pattern
  deriving Repr, Ord, Hashable, DecidableEq

instance : Inhabited PatternValidated where
  default := ⟨[.oneStar], by simp [isValidSequence]⟩

open Lean Meta Elab

-- Helper function to create decidable proofs (same as in the regex library)
private def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

-- Now the main ToExpr instance for PatternValidated
instance : ToExpr PatternValidated where
  toTypeExpr := mkConst ``PatternValidated
  toExpr pv :=
    let patternExpr := toExpr pv.pattern
    -- Construct a term representing `isValidSequence pv.pattern` using a decidable instance
    let validType := mkApp (mkConst ``isValidSequence) patternExpr
    let validInstance := mkApp (mkConst ``isValidSequenceDecidable) patternExpr
    let validProof := mkDecidableProof validType validInstance
    -- Construct the final PatternValidated.mk expression
    mkApp2 (mkConst ``PatternValidated.mk) patternExpr validProof

inductive PatternValidatedError where
  | invalidEmpty : PatternValidatedError
  | invalidWrongOrdering : PatternValidatedError
  deriving Repr, Ord, Hashable, DecidableEq

def PatternValidatedError.toHumanReadable : PatternValidatedError → String
  | .invalidEmpty => "Pattern cannot be empty."
  | .invalidWrongOrdering => r#"Pattern doesn't follow rules:
  1. Double stars can follow only * or "foo" (**/** is disallowed).
  2. One stars can follow only * or "foo" (**/* is disallowed)."#

def PatternValidated.mk? (segments : List PatternSegmentNonWF) : Except PatternValidatedError PatternValidated :=
  if h : isValidSequence segments then .ok ⟨segments, h⟩ else .error (if segments = [] then .invalidEmpty else .invalidWrongOrdering)

--------------------------------------

-- rules:
-- ✅ "**/foo/**"
#guard isValidSequence (patternNonWFLax "**/foo/**") = True
#guard (PatternValidated.mk? (patternNonWFLax "**/foo/**")).isOk

-- ⛔ "" (empty list)
#guard isValidSequence (patternNonWFLax "") = False
#guard (PatternValidated.mk? (patternNonWFLax "")).isOk.not

-- ⛔ "**/**" (** cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, .doubleStar]).isOk.not

-- ⛔ "**/*/**" (* cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, .oneStar, .doubleStar]).isOk.not

-- ✅ "foo/*/**"
#guard (PatternValidated.mk? [nes!"foo", .oneStar, .doubleStar]).isOk

-- ✅ "**/foo/*/**" (** can be after *)
#guard (PatternValidated.mk? [.doubleStar, nes!"foo", .oneStar, .doubleStar]).isOk

-- ⛔ "**/foo/**/*" (* cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, nes!"foo", .doubleStar, .oneStar]).isOk.not

-- ⛔ "**/*/foo/**" (* cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, .oneStar, nes!"foo", .doubleStar]).isOk.not

-- ✅ "*/**/foo/**" (** can be after *)
#guard (PatternValidated.mk? [.oneStar, .doubleStar, nes!"foo", .doubleStar]).isOk

-- ✅ "**/foo/**/bar/**"
#guard (PatternValidated.mk? [.doubleStar, nes!"foo", .doubleStar, nes!"bar", .doubleStar]).isOk

-----------------------------

def PatternValidated.patternStrict? (str : String) : Except String PatternValidated :=
  match PatternNonWF'.fromStringStrict str with
  | .none => throw "Did some segment was empty? `foo//bar` should be `foo/bar`"
  | .some pat => match (PatternValidated.mk? pat) with
    | .error .invalidEmpty => throw PatternValidatedError.invalidEmpty.toHumanReadable
    | .error .invalidWrongOrdering => throw (s!"Probably You wanted to write {PatternNonWF'.toString $ normalizeSegments pat}\n{PatternValidatedError.invalidWrongOrdering.toHumanReadable}")
    | .ok pat => return pat

def PatternValidated.patternStrictIO! (str : String) : IO PatternValidated := do
  match PatternValidated.patternStrict? str with
  | .ok  pat => pure pat
  | .error err => throw <| IO.userError err
