import LSpec
import Glob.NonWF.Normalize
import Glob.WF.Types
import Test.LSpec.List
import Test.LSpec.NonEmptyList
import Test.LSpec.String
import Test.LSpec.NonEmptyString
import Test.LSpec.PatternSegmentNonWF
open LSpec SlimCheck Gen

namespace NormalizeReturnsIsValidSpec

instance : Shrinkable PatternSegmentNonWF := Shrinkable.mk PatternSegmentNonWF.shrink

instance [Shrinkable a] : Shrinkable (NonEmptyList a) := Shrinkable.mk NonEmptyList.shrink

instance [Shrinkable α] : Shrinkable (List α) := Shrinkable.mk List.shrink

instance : Shrinkable PatternSegmentNonWF := {}

instance : Shrinkable (NonEmptyList PatternSegmentNonWF) := {}

instance : SampleableExt PatternSegmentNonWF :=
  SampleableExt.mkSelfContained genPatternSegmentNonWF

instance : SampleableExt (List PatternSegmentNonWF) :=
  SampleableExt.mkSelfContained (listOf genPatternSegmentNonWF)

instance : SampleableExt (NonEmptyList PatternSegmentNonWF) :=
  SampleableExt.mkSelfContained (nonEmptyListOf genPatternSegmentNonWF)

#lspec check "normalize gives isValid path in output"
  (∀ globPath : NonEmptyList PatternSegmentNonWF, isValidSequence (normalizeSegments globPath.toList))

-- #lspec test "normalize gives isValid path in output" $
--   forAllSuchThat (listOf genSegment) (λ xs => xs ≠ []) fun xs => do
--     let result := isValidSequence (normalizeSegments xs)
--     unless result do
--       throwTestFailure s!"normalize output is not valid: {xs}"

-- #lspec test "normalize gives isValid path in output"
  -- (∀ globPath, globPath ≠ [] → isValidSequence (normalizeSegments globPath))
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

end NormalizeReturnsIsValidSpec
