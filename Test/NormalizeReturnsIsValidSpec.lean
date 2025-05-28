import LSpec
import Glob.NonWF.Normalize
import Glob.WF

open LSpec SlimCheck Gen

def genSegment : Gen PatternSegmentNonWF := do
  let i ← Gen.choose Nat 0 2
  match i with
  | 0 => return PatternSegmentNonWF.doubleStar
  | 1 => return PatternSegmentNonWF.oneStar
  | _ => do
    let lit ← Gen.elements #["foo", "bar", "baz"]
    if h : lit ≠ "" then
      return PatternSegmentNonWF.lit ⟨lit, h⟩
    else
      return PatternSegmentNonWF.lit ⟨"x", by decide⟩

instance : Shrinkable PatternSegmentNonWF :=
  Shrinkable.mk (fun _ => [])

instance : Shrinkable (List PatternSegmentNonWF) :=
  Shrinkable.mk (fun _ => [])

instance : SampleableExt PatternSegmentNonWF :=
  SampleableExt.mkSelfContained genSegment

instance : SampleableExt (List PatternSegmentNonWF) :=
  SampleableExt.mkSelfContained (listOf genSegment)

#lspec check "normalize gives isValid path in output" $
  ∀ globPath : List PatternSegmentNonWF, isValidSequence (normalizeSegments globPath)
  -- (∀ globPath : List PatternSegmentNonWF, isValidSequence (normalizeSegments (/- dbgTraceVal -/ globPath)))
  -- (∀ globPath : List PatternSegmentNonWF, (normalizeSegments globPath) ≠ [])

def suite := [
  check "normalize gives non-empty result" (∀ globPath : List PatternSegmentNonWF, (normalizeSegments globPath) ≠ [])
]

-- Sampling instance for list of sampleable items
-- instance {α : Type} [SampleableExt α] : SampleableExt (List α) :=
  -- SampleableExt.mkSelfContained (listOf (SampleableExt.sample α))

/- def tests : TestSuite := -/
/-   checkAll "example tests" [ -/
/-     ("1 + 1 = 2", 1 + 1 = 2), -/
/-     ("2 * 2 = 4", 2 * 2 = 4) -/
/-   ] -/

-- #lspec check "normalize gives isValid path in output" $
--   checkAll (List PatternSegmentNonWF) "globPath" fun globPath =>
--     isValidSequence (normalizeSegments globPath)

-- #lspec check "normalize gives isValid path in output" $ ∀ globPath : List PatternSegmentNonWF, isValidSequence (normalizeSegments globPath)
