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
import Glob.NonWF

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

-------------

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
  | [] => True
  | [_] => True
  | prev :: next :: rest => canFollow prev next ∧ isValidSequence (next :: rest)

structure PatternValidated : Type where
  pattern : List PatternSegmentNonWF
  valid_sequence : isValidSequence pattern
  deriving Repr, Ord, Hashable, DecidableEq

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
  | [] => isTrue (by simp [isValidSequence])
  | [_] => isTrue trivial
  | prev :: next :: rest =>
    match canFollowDecidable prev next, isValidSequenceDecidable (next :: rest) with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h, _ => isFalse (by intro ⟨h', _⟩; exact h h')
    | _, isFalse h => isFalse (by intro ⟨_, h'⟩; exact h h')

def validatePattern (segments : List PatternSegmentNonWF) : Option PatternValidated :=
  if h : isValidSequence segments then some ⟨segments, h⟩ else none

-- rules:
-- ✅ "**/foo/**"
#guard isValidSequence (patternNonWFLax "**/foo/**") = True
#guard (validatePattern (patternNonWFLax "**/foo/**")).isSome

-- ⛔ "" (empty list)
#guard isValidSequence (patternNonWFLax "") = True
#guard (validatePattern (patternNonWFLax "")).isSome

-- ⛔ "**/**" (** cannot be after **)
#guard validatePattern [.doubleStar, .doubleStar] = .none

-- ⛔ "**/*/**" (* cannot be after **)
#guard validatePattern [.doubleStar, .oneStar, .doubleStar] = .none

-- ✅ "foo/*/**"
#guard (validatePattern [nes!"foo", .oneStar, .doubleStar]).isSome

-- ✅ "**/foo/*/**" (** can be after *)
#guard (validatePattern [.doubleStar, nes!"foo", .oneStar, .doubleStar]).isSome

-- ⛔ "**/foo/**/*" (* cannot be after **)
#guard validatePattern [.doubleStar, nes!"foo", .doubleStar, .oneStar] = .none

-- ⛔ "**/*/foo/**" (* cannot be after **)
#guard validatePattern [.doubleStar, .oneStar, nes!"foo", .doubleStar] = .none

-- ✅ "*/**/foo/**" (** can be after *)
#guard (validatePattern [.oneStar, .doubleStar, nes!"foo", .doubleStar]).isSome

-- ✅ "**/foo/**/bar/**"
#guard (validatePattern [.doubleStar, nes!"foo", .doubleStar, nes!"bar", .doubleStar]).isSome
