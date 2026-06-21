namespace String

/--
A chain of valid cut positions inside a string, strictly increasing, all lying strictly between
a lower bound `lo` and a fixed upper bound `hi`.

`Cutter str lo hi` witnesses enough information to split the region `[lo, hi)` of `str` into a
list of `String.Slice` pieces with no need for `panic!`, since every boundary inequality needed
to build a `Slice` is carried along by the constructors.
-/
inductive Cutter (str : String) : str.Pos → str.Pos → Type where
  /-- No further cuts: the whole remaining region `[lo, hi)` becomes one slice. -/
  | nil {lo hi : str.Pos} (h : lo ≤ hi) : Cutter str lo hi
  /-- Cut at `p`, with `lo < p < hi`, then keep cutting the rest of `[p, hi)`. -/
  | cons {lo hi : str.Pos} (p : str.Pos) (hlo : lo < p) (hp : p < hi)
      (rest : Cutter str p hi) : Cutter str lo hi

/-- Build a `String.Slice` from two ordered positions on the same string. -/
@[inline]
def Pos.sliceBetween {str : String} (a b : str.Pos) (h : a ≤ b) : String.Slice where
  str := str
  startInclusive := a
  endExclusive := b
  startInclusive_le_endExclusive := h

/-- Turn a cut chain into the list of slices it describes, left to right. -/
def Cutter.toList {str : String} {lo hi : str.Pos} : Cutter str lo hi → List String.Slice
  | .nil h => [Pos.sliceBetween lo hi h]
  | .cons p hlo hp rest => Pos.sliceBetween lo p (by grind only) :: rest.toList

end String

/-- A cutter spanning the entire string, from `startPos` to `endPos`. -/
abbrev String.FullCutter (str : String) : Type :=
  String.Cutter str str.startPos str.endPos

def String.cutFull {str : String} (c : str.FullCutter) : List String.Slice :=
  c.toList

/-- A cutter spanning an entire slice, useful for re-cutting an existing slice. -/
abbrev String.Slice.CutterFor (s : String.Slice) : Type :=
  String.Cutter s.str s.startInclusive s.endExclusive

def String.Slice.cut {s : String.Slice} (c : s.CutterFor) : List String.Slice :=
  c.toList


example (p1 p2 p3 : "abcde".Pos)
    (h1 : "abcde".startPos < p1) (h2 : p1 < p2) (h3 : p2 < p3) (h4 : p3 < "abcde".endPos) :
    "abcde".FullCutter :=
  .cons p1 h1 (by grind only) <|
  .cons p2 h2 (by grind only) <|
  .cons p3 h3 (by grind only) <|
  .nil (by grind only)


section
def s : String := "𝒫(A)"

-- Cutting at valid character boundaries (after 𝒫, after `(`) typechecks fine:
example : s.FullCutter :=
  let p1 : s.Pos := s.pos ⟨4⟩ (by decide)  -- boundary right after 𝒫
  let p2 : s.Pos := s.pos ⟨5⟩ (by decide)  -- boundary right after (
  .cons p1 (by decide) (by decide) <|
  .cons p2 (by decide) (by decide) <|
  .nil (by decide)

-- Trying to cut *inside* 𝒫 (byte offset 1, 2, or 3) is simply not a valid position,
-- so `s.pos ⟨1⟩ _` cannot even be constructed:
example : ¬ (⟨1⟩ : String.Pos.Raw).IsValid s := by decide

-- This fails to elaborate, since no proof of `IsValid` exists for offset 1:
-- def bad : s.Pos := s.pos ⟨1⟩ (by decide)   -- `decide` fails here
end
