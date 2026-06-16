module
public import LSpec
public import Glob.NonWF.Normalize
public import Glob.WF.Types
public import GlobTest.LSpec.List
public import GlobTest.LSpec.NonEmptyList
public import GlobTest.LSpec.String
public import GlobTest.LSpec.NonEmptyString
public import GlobTest.LSpec.PatternSegmentNonWF

@[expose] public section

open LSpec SlimCheck Gen

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

def suite := [
  check "normalize gives non-empty result" (∀ globPath : List PatternSegmentNonWF, (normalizeSegments globPath) ≠ [])
]

end NormalizeReturnsIsValidSpec
