import Mathlib
open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false
universe u

theorem String.Slice.foldr_eq_revChars_foldl {α : Type u}
    (f : Char → α → α) (init : α) (s : String.Slice) :
    s.foldr f init = (s.revChars.toList).foldl (flip f) init := by
  rw [String.Slice.foldr, ← Std.Iter.foldl_toList]

theorem String.foldr_eq_revChars_foldl {α : Type u}
    (f : Char → α → α) (init : α) (s : String) :
    s.foldr f init = (s.toSlice.revChars.toList).foldl (flip f) init := by
  rw [String.foldr, String.Slice.foldr_eq_revChars_foldl]

/-- External lemma to unfold `pure x` in the `Id` monad. -/
theorem hpure_Id {α : Type} (x : α) : (pure x : Id α) = x := rfl

/-- Recursive tactic to advance the backward iterator step-by-step.
By chaining the steps with `<;>` and recursing inside a `first | ... | skip` block,
we avoid sequence typing issues and loop until the iterator is fully resolved. -/
syntax "repeat_step" : tactic

macro_rules
  | `(tactic| repeat_step) => `(tactic|
    first
    | (rw [Std.Iter.toList_eq_match_step] <;>
       simp (config := { decide := true }) only [
         Std.Iter.step, Std.IterM.step, Std.Iterator.step, String.Slice.revPositions,
         Std.Iter.toIterM, Id.run, hpure_Id, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure,
         Std.IterStep.mapIterator_yield, Std.IterStep.mapIterator_done,
         dif_pos, dif_neg, List.map_cons, List.map_nil, List.cons.injEq, and_true
       ]) <;>
      repeat_step
    | skip
  )

/-- Main tactic to prove `"..." .utf16Length ≤ N` for concrete string literals.
We chain everything with `<;>` to ensure it is typed as a single `tactic` and avoids
any syntax ambiguities with semicolon sequences. -/
macro "prove_utf16Length_le" : tactic => `(tactic|
  (rw [String.utf16Length, String.foldr_eq_revChars_foldl] <;>
   rw [String.Slice.revChars, Std.Iter.toList_map] <;>
   repeat_step <;>
   simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] <;>
   decide)
)

-- ==========================================
-- Examples
-- ==========================================

example : "x".utf16Length ≤ 255 := by prove_utf16Length_le
example : "".utf16Length ≤ 0 := by prove_utf16Length_le
example : "hello".utf16Length ≤ 5 := by prove_utf16Length_le
example : "🚀".utf16Length ≤ 2 := by prove_utf16Length_le
example : "Lean 4 is awesome! 💻".utf16Length ≤ 30 := by prove_utf16Length_le
example : "".utf16Length ≤ 1 := by prove_utf16Length_le
example : "a".utf16Length ≤ 1 := by prove_utf16Length_le
example : "ok".utf16Length ≤ 2 := by prove_utf16Length_le

example : "decidability".utf16Length ≤ 15 := by prove_utf16Length_le
example : "constructor".utf16Length ≤ 20 := by prove_utf16Length_le
example : "unification".utf16Length ≤ 15 := by prove_utf16Length_le
example : "isomorphic".utf16Length ≤ 10 := by prove_utf16Length_le
example : "你好".utf16Length ≤ 5 := by prove_utf16Length_le
example : "中文".utf16Length ≤ 2 := by prove_utf16Length_le
example : "日本語".utf16Length ≤ 5 := by prove_utf16Length_le
example : "こんにちは".utf16Length ≤ 10 := by prove_utf16Length_le
example : "한국어".utf16Length ≤ 5 := by prove_utf16Length_le
example : "안녕하세요".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Привет".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Bonjour".utf16Length ≤ 15 := by prove_utf16Length_le
example : "Guten Tag".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Hola".utf16Length ≤ 5 := by prove_utf16Length_le
example : "Ciao".utf16Length ≤ 4 := by prove_utf16Length_le
example : "שלوم".utf16Length ≤ 10 := by prove_utf16Length_le
example : "مرحبا".utf16Length ≤ 10 := by prove_utf16Length_le
example : "नमस्ते".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Ω".utf16Length ≤ 5 := by prove_utf16Length_le
example : "x = y".utf16Length ≤ 10 := by prove_utf16Length_le
example : "∀x, x = x".utf16Length ≤ 15 := by prove_utf16Length_le
example : "a ∈ S".utf16Length ≤ 10 := by prove_utf16Length_le
example : "A ⊆ B".utf16Length ≤ 5 := by prove_utf16Length_le
example : "∅ ⊆ A".utf16Length ≤ 10 := by prove_utf16Length_le
example : "α + β".utf16Length ≤ 5 := by prove_utf16Length_le
example : "π ≈ 3.14".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Lean 💻".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Code 🚀".utf16Length ≤ 10 := by prove_utf16Length_le
example : "Math 🍎".utf16Length ≤ 8 := by prove_utf16Length_le
example : "1 + 2 = 3".utf16Length ≤ 10 := by prove_utf16Length_le
example : "a ≠ b".utf16Length ≤ 10 := by prove_utf16Length_le
example : "x ∉ ∅".utf16Length ≤ 5 := by prove_utf16Length_le
example : "A ∩ B".utf16Length ≤ 10 := by prove_utf16Length_le
example : "A ∪ B".utf16Length ≤ 5 := by prove_utf16Length_le

-- Visually 1 grapheme, but actually 5 UTF-16 code units
example : "🧑‍💻".utf16Length ≤ 5 := by prove_utf16Length_le
-- Visually 1 grapheme, but actually 4 UTF-16 code units
example : "👍🏾".utf16Length ≤ 4 := by prove_utf16Length_le
-- 3. Decomposed 'e' + combining accent (Length = 2)
example : "é".utf16Length ≤ 2 := by prove_utf16Length_le
-- 4. Precomposed 'é' (Length = 1)
example : "é".utf16Length ≤ 1 := by prove_utf16Length_le
-- Visually 1 flag, but actually 4 UTF-16 code units
example : "🇰🇭".utf16Length ≤ 4 := by prove_utf16Length_le
-- 3 ancient symbols, but 6 UTF-16 code units
example : "𓀀𓀁𓀂".utf16Length ≤ 6 := by prove_utf16Length_le
-- "a\tb\nc" contains 5 code units (escapes are resolved to size 1)
example : "a\tb\nc".utf16Length ≤ 5 := by prove_utf16Length_le
example : "a🚀b💻c🍎d".utf16Length ≤ 10 := by prove_utf16Length_le
