import Init.System.IO
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Init.Meta
import Lean.Parser.Term
import Glob.NonEmptyString
import Glob.NonEmptyList
import Glob.NEFromTo
import Mathlib.Data.List.Induction
import Aesop
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
  | [] => False
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
  | [] => isFalse (by simp [isValidSequence])
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
#guard (isValidSequence [.doubleStar, nes!"foo", .doubleStar]) = True
#guard (validatePattern [.doubleStar, nes!"foo", .doubleStar]).isSome

-- ⛔ "" (empty list)
#guard (isValidSequence []) = False
#guard (validatePattern []).isNone

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

lemma canFollow_anything_lit (prev : PatternSegmentNonWF) (s : NonEmptyString) :
    canFollow prev (.lit s) := by
  simp [canFollow]

lemma isValidSequence_append_lit (segments : List PatternSegmentNonWF) (s : NonEmptyString)
    (h : isValidSequence segments) : isValidSequence (segments ++ [.lit s]) := by
  induction segments with
  | nil =>
    simp [isValidSequence]
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [isValidSequence]
      exact canFollow_anything_lit head s
    | cons head2 tail2 =>
      simp [isValidSequence] at h ⊢
      constructor
      · exact h.1
      · exact ih h.2

lemma isValidSequence_cons_cons (a b : PatternSegmentNonWF) (rest : List PatternSegmentNonWF) :
    isValidSequence (a :: b :: rest) ↔ canFollow a b ∧ isValidSequence (b :: rest) := by
  simp [isValidSequence]

-- Helper lemmas for canFollow rules
lemma canFollow_lit_oneStar (s : NonEmptyString) : canFollow (.lit s) .oneStar := by
  simp [canFollow]

lemma canFollow_lit_doubleStar (s : NonEmptyString) : canFollow (.lit s) .doubleStar := by
  simp [canFollow]

lemma isValidSequence_append_oneStar (segments : List PatternSegmentNonWF)
    (h : isValidSequence segments)
    (lastIsLit : ∃ s, segments.getLast? = some (.lit s)) :
    isValidSequence (segments ++ [.oneStar]) := by
  obtain ⟨s, hlast⟩ := lastIsLit
  induction segments with
  | nil =>
    simp at hlast
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [List.getLast?] at hlast
      subst hlast
      simp [isValidSequence]
      exact canFollow_lit_oneStar s
    | cons head2 tail2 =>
      simp [isValidSequence] at h ⊢
      constructor
      · exact h.1
      · simp_all only [List.cons_append, forall_const, List.getLast?_cons_cons]

lemma isValidSequence_append_doubleStar (segments : List PatternSegmentNonWF)
    (h : isValidSequence segments)
    (lastIsLit : ∃ s, segments.getLast? = some (.lit s)) :
    isValidSequence (segments ++ [.doubleStar]) := by
  obtain ⟨s, hlast⟩ := lastIsLit
  induction segments with
  | nil =>
    simp at hlast
  | cons head tail ih =>
    cases tail with
    | nil =>
      simp [List.getLast?] at hlast
      subst hlast
      simp [isValidSequence]
      exact canFollow_lit_doubleStar s
    | cons head2 tail2 =>
      simp [isValidSequence] at h ⊢
      constructor
      · exact h.1
      · simp_all only [List.cons_append, forall_const, List.getLast?_cons_cons]

-- Smart constructors that maintain validity
def PatternValidated.single (seg : PatternSegmentNonWF) : PatternValidated :=
  ⟨[seg], by simp [isValidSequence]⟩

def PatternValidated.addOneStar (pv : PatternValidated) : Option PatternValidated :=
  match h : pv.pattern.getLast? with
  | some (.lit s) =>
    some ⟨pv.pattern ++ [.oneStar],
          isValidSequence_append_oneStar pv.pattern pv.valid_sequence ⟨s, h⟩⟩
  | _ => none

def PatternValidated.addDoubleStar (pv : PatternValidated) : Option PatternValidated :=
  match h : pv.pattern.getLast? with
  | some (.lit s) =>
    some ⟨pv.pattern ++ [.doubleStar],
          isValidSequence_append_doubleStar pv.pattern pv.valid_sequence ⟨s, h⟩⟩
  | _ => none

def PatternValidated.addLit (pv : PatternValidated) (s : NonEmptyString) : PatternValidated :=
  ⟨pv.pattern ++ [.lit s], isValidSequence_append_lit pv.pattern s pv.valid_sequence⟩

-- PatternValidated extensionality
lemma PatternValidated.ext (pv1 pv2 : PatternValidated)
    (h : pv1.pattern = pv2.pattern) : pv1 = pv2 := by
  cases pv1 with
  | mk p1 h1 =>
    cases pv2 with
    | mk p2 h2 =>
      simp at h
      subst h
      congr

#guard (PatternValidated.single .doubleStar |>.addLit (nes!"foo") |>.addDoubleStar).map (·.pattern) = .some [.doubleStar, nes!"foo", .doubleStar]

-- | Input Pattern                            | Usually Parsed As                                         | Should be normalized to equivalent
-- | ----------------------------             | ---------------------------------------                   | ------------------------------------
-- | `""`                                     | `[]`                                                      | `[]`
-- | `"**"`                                   | `[**]`                                                    | `[**]`
-- | `"*"`                                    | `[*]`                                                     | `[*]`
-- | `"**/*"`                                 | `[**, *]`                                                 | `[*, **]`
-- | `"**/**"`                                | `[**, **]`                                                | `[**]`
-- | `"**/foo.txt"`                           | `[**, "foo.txt"]`                                         | `[**, "foo.txt"]`
-- | `"*/foo.txt"`                            | `[*,"foo.txt"]`                                           | `[*, "foo.txt"]`
-- | `"*/*/foo.txt"`                          | `[* , *, "foo.txt"]`                                      | `[*, *, "foo.txt"]`
-- | `"*/*/**/*/*/foo.txt"`                   | `[* , *, **, *, *, "foo.txt"]`                            | `[*, *, *, *, **, "foo.txt"]`
-- | `"**/*/*"`                               | `[**, *, *]`                                              | `[*, *, **]`
-- | `"foo/bar.txt"`                          | `["foo", "bar.txt"]`                                      | `["foo", "bar.txt"]`
-- | `"**/foo/*/bar.txt"`                     | `[**, "foo", *, "bar.txt"]`                               | `[**, "foo", *, "bar.txt"]`
-- | `"**/foo/**/bar.txt"`                    | `[**, "foo", **, "bar.txt"]`                              | `[**, "foo", **, "bar.txt"]`
-- | `"**/foo/**/**/bar.txt"`                 | `[**, "foo", **, **, "bar.txt"]`                          | `[**, "foo", **, "bar.txt"]`
-- | `"**/foo/**/baz/**/bar.txt"`             | `[**, "foo", **, "baz", **, "bar.txt"]`                   | `[**, "foo", **, "baz", **, "bar.txt"]`
-- | `"*/**/*/foo/*/**/*/baz/*/**/*/bar.txt"` | `[*, **, *, "foo", *, **, *, "baz", *, **, *, "bar.txt"]` | `[*, *, **, "foo", *, *, **, "baz", *, *, **, "bar.txt"]`

------------------------------

def normalizeSegmentsGo (acc : List PatternSegmentNonWF) (remaining : List PatternSegmentNonWF) : List PatternSegmentNonWF :=
  match remaining with
  | [] => acc
  | [x] => (x :: acc)
  | .doubleStar :: .doubleStar :: rest => normalizeSegmentsGo acc (.doubleStar :: rest)
  | .doubleStar :: .oneStar :: rest => normalizeSegmentsGo (.oneStar :: acc) (.doubleStar :: rest)
  | x :: rest => normalizeSegmentsGo (x :: acc) rest

def normalizeSegments (ps : List PatternSegmentNonWF) : List PatternSegmentNonWF := (normalizeSegmentsGo [] ps).reverse

#guard normalizeSegments (patternNonWFLax "") == (patternNonWFLax "")
#guard normalizeSegments (patternNonWFLax "**") == (patternNonWFLax "**")
#guard normalizeSegments (patternNonWFLax "*") == (patternNonWFLax "*")
#guard normalizeSegments (patternNonWFLax "**/*") == (patternNonWFLax "*/**")
#guard normalizeSegments (patternNonWFLax "**/**") == (patternNonWFLax "**")
#guard normalizeSegments (patternNonWFLax "**/foo.txt") == (patternNonWFLax "**/foo.txt")
#guard normalizeSegments (patternNonWFLax "*/foo.txt") == (patternNonWFLax "*/foo.txt")
#guard normalizeSegments (patternNonWFLax "*/*/foo.txt") == (patternNonWFLax "*/*/foo.txt")
#guard normalizeSegments (patternNonWFLax "*/*/**/*/*/foo.txt") == (patternNonWFLax "*/*/*/*/**/foo.txt")
#guard normalizeSegments (patternNonWFLax "**/*/*") == (patternNonWFLax "*/*/**")
#guard normalizeSegments (patternNonWFLax "foo/bar.txt") == (patternNonWFLax "foo/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/*/bar.txt") == (patternNonWFLax "**/foo/*/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/**/bar.txt") == (patternNonWFLax "**/foo/**/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/**/**/bar.txt") == (patternNonWFLax "**/foo/**/bar.txt")
#guard normalizeSegments (patternNonWFLax "**/foo/**/baz/**/bar.txt") == (patternNonWFLax "**/foo/**/baz/**/bar.txt")
#guard normalizeSegments (patternNonWFLax "*/**/*/foo/*/**/*/baz/*/**/*/bar.txt") == (patternNonWFLax "*/*/**/foo/*/*/**/baz/*/*/**/bar.txt")


-- First, let's make normalizeSegments more principled and prove properties about it

-- A more structured approach to normalization that preserves validity
def normalizeSegmentsValid (ps : List PatternSegmentNonWF) (h : isValidSequence ps) :
  { result : List PatternSegmentNonWF // isValidSequence result ∧ result ≠ [] } :=
  -- We'll prove that normalization preserves validity
  sorry

def isNormalized (ps : List PatternSegmentNonWF) : Prop :=
  (∀ i, ps[i]? = some .doubleStar → ps[i + 1]? ≠ some .doubleStar) ∧
  (∀ i, ps[i]? = some .doubleStar → ps[i + 1]? ≠ some .oneStar)

-- Lemma: all valid sequences are already normalized
lemma valid_implies_normalized (ps : List PatternSegmentNonWF) (h : isValidSequence ps) :
  isNormalized ps := by
  constructor
  · intro i hi
    -- Use the fact that canFollow .doubleStar .doubleStar = False
    sorry
  · intro i hi
    -- Use the fact that canFollow .doubleStar .oneStar = False
    sorry


-- Prove that normalization preserves the empty list
lemma normalizeSegmentsCorrect_empty :
  normalizeSegmentsCorrect [] = [] := by
  aesop

-- Prove that normalization is idempotent
lemma normalizeSegmentsCorrect_idempotent (ps : List PatternSegmentNonWF) :
  normalizeSegmentsCorrect (normalizeSegmentsCorrect ps) = normalizeSegmentsCorrect ps := by
  sorry

-- Key lemma: normalization doesn't change valid sequences
lemma normalizeSegmentsCorrect_valid_unchanged (ps : List PatternSegmentNonWF) (h : isValidSequence ps) :
  normalizeSegmentsCorrect ps = ps := by
  have norm : isNormalized ps := valid_implies_normalized ps h
  -- Since ps is already normalized, normalization doesn't change it
  sorry

-- Now we can prove properties about the normalize function
lemma normalize_on_validated (pv : PatternValidated) :
  ∃ (h : pv.pattern ≠ []), normalize pv.pattern h = pv := by
  -- We need to show that normalize preserves the pattern and proof
  use (by
    cases pv.pattern with
    | nil => simp [isValidSequence] at pv.valid_sequence
    | cons => simp)
  -- The key insight is that makeValid should reconstruct the same pattern
  -- when given an already valid input
  sorry

-- Alternative approach: make normalize total and prove identity directly
def normalizeTotal (ps : List PatternSegmentNonWF) : Option PatternValidated :=
  match ps with
  | [] => none
  | _ =>
    let normalized := normalizeSegmentsCorrect ps
    validatePattern normalized

-- This version is easier to work with
lemma normalizeTotal_validated_identity (pv : PatternValidated) :
  normalizeTotal pv.pattern = some pv := by
  simp [normalizeTotal]
  have h_ne : pv.pattern ≠ [] := by
    cases pv.pattern with
    | nil => simp [isValidSequence] at pv.valid_sequence
    | cons => simp
  simp [h_ne]
  rw [normalizeSegmentsCorrect_valid_unchanged pv.pattern pv.valid_sequence]
  simp [validatePattern]
  -- The validated pattern should validate to itself
  rw [dif_pos pv.valid_sequence]
  -- Need to show structural equality
  sorry

-- Helper lemmas you'll need to complete the proof

lemma canFollow_doubleStar_not_doubleStar (a : PatternSegmentNonWF) :
  ¬canFollow .doubleStar .doubleStar := by
  simp [canFollow]

lemma canFollow_doubleStar_not_oneStar :
  ¬canFollow .doubleStar .oneStar := by
  simp [canFollow]

-- Induction principle for isValidSequence
lemma isValidSequence_ind {P : List PatternSegmentNonWF → Prop}
  (h_single : ∀ x, P [x])
  (h_cons : ∀ x y xs, canFollow x y → isValidSequence (y :: xs) → P (y :: xs) → P (x :: y :: xs)) :
  ∀ ps, isValidSequence ps → P ps := by
  intro ps h
  cases ps with
  | nil => simp [isValidSequence] at h
  | cons x xs =>
    cases xs with
    | nil => exact h_single x
    | cons y ys =>
      simp [isValidSequence] at h
      exact h_cons x y ys h.1 h.2 (by
        aesop
        )

-- This gives you the structure to complete the proof
-- The key insight is that valid sequences satisfy the normalization invariants already

------------------------------------------------------------------------

-- Helper function to move ** segments to the right and collapse consecutive **

-- Helper function to ensure the result is valid by construction
def makeValid (ps : List PatternSegmentNonWF) (h : ps ≠ []) : PatternValidated :=
  let normalized := normalizeSegments ps
  match normalized with
  | [] =>
    -- This shouldn't happen given our precondition, but we need to handle it
    have : ps ≠ [] := h
    -- We can construct a single element pattern as fallback
    match ps with
    | [] => absurd rfl h
    | x :: _ => PatternValidated.single x
  | x :: xs =>
    -- Build the pattern incrementally to ensure validity
    let rec buildValid (base : PatternValidated) (remaining : List PatternSegmentNonWF) : PatternValidated :=
      match remaining with
      | [] => base
      | .lit s :: rest => buildValid (base.addLit s) rest
      | .oneStar :: rest =>
          match base.addOneStar with
          | some newBase => buildValid newBase rest
          | none => buildValid (PatternValidated.single .oneStar) rest
      | .doubleStar :: rest =>
          match base.addDoubleStar with
          | some newBase => buildValid newBase rest
          | none => buildValid (PatternValidated.single .doubleStar) rest
    buildValid (PatternValidated.single x) xs

def normalize (ps : List PatternSegmentNonWF) (h : ps ≠ []) : PatternValidated :=
  makeValid ps h

-- Helper lemma: valid sequences don't have ** followed by * or **
-- lemma valid_no_bad_double_star (ps : List PatternSegmentNonWF)
--     (h_valid : isValidSequence ps) :
--     ∀ i, ps[i]? = some .doubleStar →
--          ps[i + 1]? ≠ some .oneStar ∧ ps[i + 1]? ≠ some .doubleStar := by
--   intro i h_get
--   -- We prove by strong induction on the list
--   induction ps using List.rec with
--   | nil => simp at h_get
--   | cons head tail =>
--     cases tail with
--     | nil =>
--       simp_all only [List.getElem?_nil, reduceCtorEq, List.length_nil, Nat.not_lt_zero, List.getElem?_eq_getElem, ne_eq,
--           Option.some.injEq, IsEmpty.forall_iff, implies_true, List.getElem?_cons_succ, not_false_eq_true, and_self]
--     | cons second rest =>
--       simp [isValidSequence] at h_valid
--       have ⟨h_follow, h_valid_tail⟩ := h_valid
--       cases i with
--       | zero =>
--         rename_i tail_ih
--         simp_all only [and_self, List.length_cons, Nat.zero_lt_succ, List.getElem?_eq_getElem, List.getElem_cons_zero,
--           Option.some.injEq, Nat.zero_add, List.getElem?_cons_succ, ne_eq, forall_const, Nat.lt_add_left_iff_pos,
--           List.getElem_cons_succ]
--         subst h_get
--         apply And.intro
--         · apply Aesop.BuiltinRules.not_intro
--           intro a
--           subst a
--           simp_all only [reduceCtorEq, IsEmpty.forall_iff]
--           exact h_follow
--         · apply Aesop.BuiltinRules.not_intro
--           intro a
--           subst a
--           simp_all only [forall_const]
--           obtain ⟨left, right⟩ := tail_ih
--           exact h_follow
--       | succ j =>
--         rename_i tail_ih
--         simp_all only [and_self, List.getElem?_cons_succ, ne_eq, forall_const]
--         apply And.intro
--         · apply Aesop.BuiltinRules.not_intro
--           intro a
--           simp_all only [Option.some.injEq, reduceCtorEq, IsEmpty.forall_iff]
--           sorry
--           -- tactic 'aesop' failed, made no progress
--           -- Initial goal:
--           --   case cons.cons.succ.left.h
--           -- head second : PatternSegmentNonWF
--           -- rest : List PatternSegmentNonWF
--           -- h_follow : canFollow head second
--           -- h_valid_tail : isValidSequence (second :: rest)
--           -- j : ℕ
--           -- h_get : (second :: rest)[j]? = some PatternSegmentNonWF.doubleStar
--           -- a : rest[j]? = some PatternSegmentNonWF.oneStar
--           -- ⊢ False
--         · apply Aesop.BuiltinRules.not_intro
--           intro a
--           simp_all only [forall_const]
--           obtain ⟨left, right⟩ := tail_ih
--           /- aesop? -/
--           -- tactic 'aesop' failed, made no progress
--           -- Initial goal:
--           --   case cons.cons.succ.right.h.intro
--           -- head second : PatternSegmentNonWF
--           -- rest : List PatternSegmentNonWF
--           -- h_follow : canFollow head second
--           -- h_valid_tail : isValidSequence (second :: rest)
--           -- j : ℕ
--           -- h_get : (second :: rest)[j]? = some PatternSegmentNonWF.doubleStar
--           -- a : rest[j]? = some PatternSegmentNonWF.doubleStar
--           -- left : ¬rest[j + 1]? = some PatternSegmentNonWF.oneStar
--           -- right : ¬rest[j + 1]? = some PatternSegmentNonWF.doubleStar
--           -- ⊢ False
--           sorry
--
-- lemma no_double_star_followed_by_star (ps : List PatternSegmentNonWF)
--     (h_valid : isValidSequence ps) :
--     ¬(.doubleStar :: .oneStar :: tail) <:+ ps := by
--   intro h_sub
--   sorry
--
--   /- have h_valid_sub : isValidSequence (.doubleStar :: .oneStar :: tail) := by -/
--   /-   apply List.Sublist.isValidSequence h_sub h_valid -/
--   /- simp [isValidSequence, canFollow] at h_valid_sub -/
--   /- exact h_valid_sub.1 -/
--
-- lemma no_double_star_followed_by_double_star (ps : List PatternSegmentNonWF)
--     (h_valid : isValidSequence ps) :
--     ¬(.doubleStar :: .doubleStar :: tail) <:+ ps := by
--   intro h_sub
--   obtain ⟨_prefix, h_eq⟩ := List.isSublist_iff_append.mp h_sub -- ERROR unknown constant 'List.isSublist_iff_append.mp'
--   -- Similar reasoning
--   sorry
--
-- -- Key lemma: normalizeSegments is identity on valid sequences
-- lemma normalizeSegments_identity_on_valid (ps : List PatternSegmentNonWF)
--     (h_valid : isValidSequence ps) : normalizeSegments ps = ps := by
--   unfold normalizeSegments
--   -- We prove that moveDoubleStar [] ps = ps when ps is valid
--   let rec aux (acc remaining : List PatternSegmentNonWF)
--       (h_acc_empty : acc = []) :
--       normalizeSegments.moveDoubleStar acc remaining = acc ++ remaining := by
--     match remaining with
--     | [] => simp [normalizeSegments.moveDoubleStar]
--     | [x] => simp [normalizeSegments.moveDoubleStar, h_acc_empty]
--     | .doubleStar :: .oneStar :: rest =>
--       -- This case contradicts validity
--       exfalso
--       have h_bad : (.doubleStar :: .oneStar :: rest) <:+ ps := by
--         sorry -- Need to track that remaining is a suffix of ps
--       exact no_double_star_followed_by_star ps h_valid h_bad
--     | .doubleStar :: .doubleStar :: rest =>
--       -- This case also contradicts validity
--       exfalso
--       have h_bad : (.doubleStar :: .doubleStar :: rest) <:+ ps := by
--         sorry -- Need to track that remaining is a suffix of ps
--       exact no_double_star_followed_by_double_star ps h_valid h_bad
--     | x :: rest =>
--       simp [List.append_assoc, h_acc_empty]
--       sorry
--
--   exact aux [] ps rfl
--
--
-- -- Main theorem: normalize is identity on valid patterns
-- theorem normalize_identity_on_valid (pv : PatternValidated) :
--     normalize pv.pattern (by
--       cases pv.pattern with
--       | nil =>
--       simp_all only [ne_eq, not_true_eq_false, pv.valid_sequence]
--       aesop
--       | cons _ _ => simp) = pv := by
--   have h_ne : pv.pattern ≠ [] := by
--     cases pv.pattern with
--     | nil => simp [isValidSequence] at pv.valid_sequence -- Error `unexpected term 'pv.valid_sequence'; expected single reference to variable`
--     | cons _ _ => simp
--
--   unfold normalize makeValid
--   have h_norm : normalizeSegments pv.pattern = pv.pattern :=
--     normalizeSegments_identity_on_valid pv.pattern pv.valid_sequence
--
--   simp [h_norm]
--   cases h_pat : pv.pattern with
--   | nil => contradiction
--   | cons head tail =>
--     -- Since the pattern is unchanged and valid, buildValid will reconstruct the same pattern
--     have h_reconstruct : makeValid.buildValid (PatternValidated.single head) tail = pv := by
--       -- This requires proving that buildValid on a valid sequence reconstructs the original
--       sorry -- Complex proof about buildValid preserving structure
--     exact h_reconstruct

-- elab "patternLax" pat:str : term => do
--   let s := pat.getString
--   return (Lean.toExpr (Pattern.fromPatternNonWF $ PatternNonWF'.fromStringLax s))
--
-- elab "patternStrict" pat:str : term => do
--   let s := pat.getString
--   match PatternNonWF.fromStringStrict s with
--   | some (p : NonEmptyList PatternSegmentNonWF) => return (Lean.toExpr p)
--   | none   => throwError s!"invalid non-well-formed pattern: {s}"
--
-- #guard Pattern.fromPatternNonWF [] = Pattern.mk .none [] .oneStar
-- #guard Pattern.fromPatternNonWF (patternNonWFLax"") = Pattern.mk .none [] .oneStar
--
-- #guard patternLax "" = Pattern.mk .none [] .oneStar
-- #guard patternLax "**" = Pattern.mk .onStartAndEnd [] .oneStar
-- #guard patternLax "*" = Pattern.mk .none [] .oneStar
-- #guard patternLax "**/*" = Pattern.mk .onStart [] .oneStar
-- #guard patternLax "**/**" = Pattern.mk .onStartAndEnd [] .oneStar
-- #guard patternLax "**/foo.txt" = Pattern.mk .onStart [] (.lit (nes! "foo.txt"))
-- #guard patternLax "*/foo.txt" = Pattern.mk .none [] .oneStar -- [nel![.oneStar]] (.lit (nes! "foo.txt"))
/- #guard patternLax "*/*/foo.txt" = Pattern.mk .none [nel![.oneStar, .oneStar]] (.lit (nes! "foo.txt")) -/
/- #guard patternLax "*/*/**/*/*/foo.txt" = Pattern.mk .none [nel![.oneStar, .oneStar], nel![.oneStar, .oneStar]] (.lit (nes! "foo.txt")) -/
/- #guard patternLax "**/*/*" = Pattern.mk .onStart [nel![.oneStar]] .oneStar -/
/- #guard patternLax "foo/bar.txt" = Pattern.mk .none [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/*/bar.txt" = Pattern.mk .onStart [nel![.lit (nes! "foo"), .oneStar]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/**/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")]] (.lit (nes! "bar.txt")) -/
/- #guard patternLax "**/foo/**/baz/**/bar.txt" = Pattern.mk .onStartAndEnd [nel![.lit (nes! "foo")], nel![.lit (nes! "baz")]] (.lit (nes! "bar.txt")) -/

def FilePath.componentsNES (p : FilePath) : List NonEmptyString :=
  ToNE.FilterMap.«LS->LNES» p.components

-- Test cases from the table:

-- | Input Pattern                | Segments Parsed                         | Output Pattern                                               |
-- | `""`                         | `[]`                                    | `none × [] × *` (just return match all files in current dir) |

-- -- | `"**"`                       | `[**]`                                  | `onStart × [] × *` (default fallback for file?)              |
-- #guard Pattern.fromPatternNonWF [.doubleStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .oneStar }

-- -- | `"*"`                        | `[*]`                                   | `none × [] × *`                                              |
-- #guard Pattern.fromPatternNonWF [.oneStar] =
--   { doubleStarOnStartOrEnd := .none, dirs := [], file := .oneStar }

-- -- | `"**/*"`                     | `[**, *]`                               | `onStart × [] × *`                                           |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .oneStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .oneStar }

-- -- | `"**/**"`                    | `[**, **]`                              | `onStart × [] × *`                                           |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .doubleStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .oneStar }

-- -- | `"**/foo.txt"`               | `[**, "foo.txt"]`                       | `onStart × [] × "foo.txt"`                                   |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [], file := .lit (nes "foo.txt") }

-- -- | `"*/foo.txt"`                | `[*,"foo.txt"]`                         | `none × [[*]] × "foo.txt"`                                   |
-- #guard Pattern.fromPatternNonWF [.oneStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.oneStar]], file := .lit (nes "foo.txt") }

-- -- | `"*/*/foo.txt"`              | `[* , *, "foo.txt"]`                    | `none × [[*,*]] × "foo.txt"`                                 |
-- #guard Pattern.fromPatternNonWF [.oneStar, .oneStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.oneStar, .oneStar]], file := .lit (nes "foo.txt") }

-- -- | `"*/*/**/*/*/foo.txt"`       | `[* , *, **, *, *, "foo.txt"]`          | `none × [[*,*], [*,*]] × "foo.txt"`                          |
-- #guard Pattern.fromPatternNonWF [.oneStar, .oneStar, .doubleStar, .oneStar, .oneStar, .lit (nes "foo.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.oneStar, .oneStar], nel![.oneStar, .oneStar]], file := .lit (nes "foo.txt") }

-- -- | `"**/*/*"`                   | `[**, *, *]`                            | `onStart × [[*]] × *`                                        |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .oneStar, .oneStar] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [nel![.oneStar]], file := .oneStar }

-- -- | `"foo/bar.txt"`              | `["foo", "bar.txt"]`                    | `none × [["foo"]] × "bar.txt"`                               |
-- #guard Pattern.fromPatternNonWF [.lit (nes "foo"), .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .none, dirs := [nel![.lit (nes "foo")]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/*/bar.txt"`         | `[**, "foo", *, "bar.txt"]`             | `onStart × [["foo", *]] × "bar.txt"`                         |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .oneStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStart, dirs := [nel![.lit (nes "foo"), .oneStar]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/**/bar.txt"`        | `[**, "foo", **, "bar.txt"]`            | `onStartAndEnd × [["foo"]] × "bar.txt"`                      |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .doubleStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStartAndEnd, dirs := [nel![.lit (nes "foo")]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/**/**/bar.txt"`     | `[**, "foo", **, **, "bar.txt"]`        | `onStartAndEnd × [["foo"]] × "bar.txt"`                      |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .doubleStar, .doubleStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStartAndEnd, dirs := [nel![.lit (nes "foo")]], file := .lit (nes "bar.txt") }

-- -- | `"**/foo/**/baz/**/bar.txt"` | `[**, "foo", **, "baz", **, "bar.txt"]` | `onStartAndEnd × [["foo"], ["baz"]] × "bar.txt"`             |
-- #guard Pattern.fromPatternNonWF [.doubleStar, .lit (nes "foo"), .doubleStar, .lit (nes "baz"), .doubleStar, .lit (nes "bar.txt")] =
--   { doubleStarOnStartOrEnd := .onStartAndEnd, dirs := [nel![.lit (nes "foo")], nel![.lit (nes "baz")]], file := .lit (nes "bar.txt") }



-- partial def walkDir
--   (p : FilePath)
--   (enter : String → Bool)
--   (shouldAddFileToListOfFilepaths : String → Bool) : IO (Array FilePath) :=
--   go p
-- where
--   go (p : FilePath) : IO (Array FilePath) := do
--     if !enter p.fileName then
--       return #[]

--     let entries ← p.readDir
--     let results ← entries.mapM fun d => do
--       let root := d.root
--       let fileName := d.fileName
--       let path := d.path
--       let includeSelf := if shouldAddFileToListOfFilepaths fileName then #[path] else #[]

--       match (← path.metadata.toBaseIO) with
--       | .ok { type := .symlink, .. } =>
--         let real ← IO.FS.realPath path
--         if (← real.isDir) then
--           -- don't call enter on symlink again
--           if enter p.fileName then
--             let sub ← go real
--             return includeSelf ++ sub
--           else
--             return includeSelf
--         else
--           return includeSelf
--       | .ok { type := .dir, .. } =>
--         let sub ← go path
--         return includeSelf ++ sub
--       | .ok =>
--         return includeSelf
--       | .error (.noFileOrDirectory ..) =>
--         return #[]
--       | .error e =>
--         throw e

--     return results.join
