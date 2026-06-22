module
public import Lean.Data.Lsp.Utf16
import all Lean.Data.Lsp.Utf16
import Init.Data.Iterators.Lemmas.Basic

/-- The backward position iterator (`revPositions`), started at a position whose split is `t₁ ++ t₂`,
enumerates the characters of `t₁` in reverse order. -/
theorem String.Slice.revPositions_toList_map (s : String.Slice) :
    ∀ (it : Std.Iter (α := RevPosIterator s) {p : s.Pos // p ≠ s.endPos})
      (t₁ t₂ : String), it.internalState.currPos.Splits t₁ t₂ →
      it.toList.map (fun x => x.1.get x.2) = t₁.toList.reverse := by
  intro it
  induction it using _root_.Std.Iter.inductSteps with
  | step it ihy _ =>
    intro t₁ t₂ h
    rw [Std.Iter.toList_eq_match_step]
    by_cases hp : it.internalState.currPos = s.startPos
    · simp only [Std.Iter.step, Std.IterM.step, Std.Iterator.step,
        Std.Iter.toIterM, Id.run, pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure,
        Std.IterStep.mapIterator_done, dif_pos hp]
      have ht1 : t₁ = "" := (h.eq_startPos_iff).mp hp
      subst ht1
      simp only [ne_eq, List.map_nil, toList_empty, List.reverse_nil]
    · simp only [Std.Iter.step, Std.IterM.step, Std.Iterator.step,
        Std.Iter.toIterM, Id.run, pure, Std.Shrink.inflate_deflate, Std.IterM.Step.toPure,
        Std.IterStep.mapIterator_yield, dif_neg hp]
      let p := it.internalState.currPos
      have hq : p.prev hp ≠ s.endPos := Slice.Pos.prev_ne_endPos
      have hqp : (p.prev hp).next hq = p := String.Slice.Pos.next_prev
      have hsplit_p : ((p.prev hp).next hq).Splits t₁ t₂ := by rw [hqp]; exact h
      obtain ⟨he1, he2⟩ := hsplit_p.eq (Slice.Pos.splits_next (p.prev hp) hq)
      have hsplit_q : (p.prev hp).Splits ((s.sliceTo (p.prev hp)).copy)
          (singleton ((p.prev hp).get hq) ++ t₂) := by
        have := Slice.Pos.splits_next_right (p.prev hp) hq
        rw [← he2] at this
        exact this
      have hstep : it.IsPlausibleStep
          (.yield ({ internalState := { currPos := p.prev hp } } :
            Std.Iter (α := RevPosIterator s) _) ⟨p.prev hp, hq⟩) := ⟨hp, rfl, rfl⟩
      have IH := ihy hstep ((s.sliceTo (p.prev hp)).copy)
        (singleton ((p.prev hp).get hq) ++ t₂) hsplit_q
      have hsingle : (singleton ((p.prev hp).get hq)).toList = [(p.prev hp).get hq] := String.toList_singleton ((p.prev hp).get hq)
      rw [List.map_cons, he1, String.toList_append, hsingle, List.reverse_append]
      simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.singleton_append]
      exact congrArg (fun l => ((p.prev hp).get hq) :: l) IH

/-- The list of characters produced by the backward (`revChars`) iterator of a string is the
reverse of the string's character list. -/
theorem String.revChars_toList_eq_reverse (s : String) :
    s.toSlice.revChars.toList = s.toList.reverse := by
  rw [String.Slice.toList_revChars, String.copy_toSlice]

/-- `String.utf16Length` in terms of public-only API, so consumers can rewrite without needing
    private access to the `csize16` helper. Proved here (once) where `import all` is in scope. -/
public theorem String.utf16Length_eq (s : String) :
    s.utf16Length = s.toList.foldr (fun c acc => c.utf16Size.toNat + acc) 0 := by
  simp only [String.utf16Length, String.foldr_eq_foldr_toList]
  rfl

-- added this (definition body/unfolding equation of Char.utf16Size) so that dont have to add `import all Lean.Data.Lsp.Utf16` in all other modules that use these theorems
public theorem Char.utf16Size_eq (c : Char) : c.utf16Size = if c.val ≤ 0xFFFF then 1 else 2 := by
  rfl

-- ==========================================
-- Examples
-- ==========================================
namespace Utf16LengthTheoremTest
example : "x".utf16Length ≤ 255 := by rw [String.utf16Length_eq]; decide
example : "".utf16Length ≤ 0 := by rw [String.utf16Length_eq]; decide
example : "hello".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "🚀".utf16Length ≤ 2 := by rw [String.utf16Length_eq]; decide
example : "Lean 4 is awesome! 💻".utf16Length ≤ 30 := by rw [String.utf16Length_eq]; decide
example : "".utf16Length ≤ 1 := by rw [String.utf16Length_eq]; decide
example : "a".utf16Length ≤ 1 := by rw [String.utf16Length_eq]; decide
example : "ok".utf16Length ≤ 2 := by rw [String.utf16Length_eq]; decide

example : "decidability".utf16Length ≤ 15 := by rw [String.utf16Length_eq]; decide
example : "constructor".utf16Length ≤ 20 := by rw [String.utf16Length_eq]; decide
example : "unification".utf16Length ≤ 15 := by rw [String.utf16Length_eq]; decide
example : "isomorphic".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "你好".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "中文".utf16Length ≤ 2 := by rw [String.utf16Length_eq]; decide
example : "日本語".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "こんにちは".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "한국어".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "안녕하세요".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Привет".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Bonjour".utf16Length ≤ 15 := by rw [String.utf16Length_eq]; decide
example : "Guten Tag".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Hola".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "Ciao".utf16Length ≤ 4 := by rw [String.utf16Length_eq]; decide
example : "שלوم".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "مرحبا".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "नमस्ते".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Ω".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "x = y".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "∀x, x = x".utf16Length ≤ 15 := by rw [String.utf16Length_eq]; decide
example : "a ∈ S".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "A ⊆ B".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "∅ ⊆ A".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "α + β".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "π ≈ 3.14".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Lean 💻".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Code 🚀".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "Math 🍎".utf16Length ≤ 8 := by rw [String.utf16Length_eq]; decide
example : "1 + 2 = 3".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "a ≠ b".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "x ∉ ∅".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "A ∩ B".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide
example : "A ∪ B".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide

-- Visually 1 grapheme, but actually 5 UTF-16 code units
example : "🧑‍💻".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
-- Visually 1 grapheme, but actually 4 UTF-16 code units
example : "👍🏾".utf16Length ≤ 4 := by rw [String.utf16Length_eq]; decide
-- 3. Decomposed 'e' + combining accent (Length = 2)
example : "é".utf16Length ≤ 2 := by rw [String.utf16Length_eq]; decide
-- 4. Precomposed 'é' (Length = 1)
example : "é".utf16Length ≤ 1 := by rw [String.utf16Length_eq]; decide
-- Visually 1 flag, but actually 4 UTF-16 code units
example : "🇰🇭".utf16Length ≤ 4 := by rw [String.utf16Length_eq]; decide
-- 3 ancient symbols, but 6 UTF-16 code units
example : "𓀀𓀁𓀂".utf16Length ≤ 6 := by rw [String.utf16Length_eq]; decide
-- "a\tb\nc" contains 5 code units (escapes are resolved to size 1)
example : "a\tb\nc".utf16Length ≤ 5 := by rw [String.utf16Length_eq]; decide
example : "a🚀b💻c🍎d".utf16Length ≤ 10 := by rw [String.utf16Length_eq]; decide

-- Tests for = and >=
example : "hello".utf16Length = 5 := by rw [String.utf16Length_eq]; decide
example : "hello".utf16Length ≥ 5 := by rw [String.utf16Length_eq]; decide
example : "🚀".utf16Length = 2 := by rw [String.utf16Length_eq]; decide
example : "🚀".utf16Length ≥ 1 := by rw [String.utf16Length_eq]; decide
