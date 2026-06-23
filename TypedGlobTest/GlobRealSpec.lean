module
public import Init.System.IO
public import Init.System.FilePath
public import LSpec
public import GlobTest.Spec.Core
public import GlobTest.Spec.Assert
public import TypedGlob.IO
public import Glob.Data.Tree

@[expose] public section

open System (FilePath)
open IO.FS
open NonEmpty.List
open NonEmpty.String
open GlobTest.Spec.Core
open GlobTest.Spec.Assert

def assertTypedGlob (tmpDir : FilePath) (pattern : PatternValidated) (expected : Array String) : IO Unit := do
  match NonEmptyList.fromList? pattern.pattern with
  | some nel =>
    let tmpPosixDir := Posix.IO.wrapAbs! .Dir tmpDir
    let actual ← typedGlobFS tmpPosixDir pattern
    let actualStrs := actual.map toString
    assertEq s!"assertTypedGlob {nel}" expected actualStrs
  | none => throw (IO.userError "Pattern cannot be empty")

def assertTypedGlobWithDirMark (tmpDir : FilePath) (pattern : PatternValidated) (expected : Array String) : IO Unit := do
  match NonEmptyList.fromList? pattern.pattern with
  | some nel =>
    let tmpPosixDir := Posix.IO.wrapAbs! .Dir tmpDir
    let actual ← typedGlobWithDirMark tmpPosixDir pattern
    let actualStrs := actual.map toString
    assertEq s!"assertTypedGlobWithDirMark {nel}" expected actualStrs
  | none => throw (IO.userError "Pattern cannot be empty")

/-- Real filesystem specs ported for TypedGlob. -/
def typedGlobRealSpec : Spec := do
  describe "TypedGlob (real filesystem)" do
    it "FindRecursive" do withinTempDirTree (tree! { "foo.txt", "subdir" { "bar.txt", "foo.txt", "another_subdir" { "bar.txt", "foo.txt" } } }) fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "**/foo.txt") [PatternSegmentNonWF.doubleStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt", "subdir/foo.txt", "subdir/another_subdir/foo.txt"]
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "foo.txt") [PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt"]
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "*/foo.txt") [PatternSegmentNonWF.oneStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["subdir/foo.txt"]

    it "BasicWildcard" do withinTempDirTree (tree! { "file1.txt", "file2.txt", "image.png", "subdir" { "file3.txt" }, "empty_dir" {} }) fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "*") [PatternSegmentNonWF.oneStar]) #["empty_dir", "file1.txt", "file2.txt", "image.png", "subdir"]

    it "QuestionMark" do withinTempDirTree (tree! { "doc1", "doc2", "doc_long" }) fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "doc?") [PatternSegmentNonWF.regex (Regex.parse! "^doc.$")]) #["doc1", "doc2"]

    it "CharacterClass" do withinTempDirTree (tree! { "apple", "apricot", "banana" }) fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "a[p-r]*") [PatternSegmentNonWF.regex (Regex.parse! "^a[p-r].*$")]) #["apple", "apricot"]

    it "GlobWithDirMark" do withinTempDirTree (tree! { "file.txt", "mydir" {}, "another_dir" {} }) fun tmpDir => do
      let expected := #["file.txt", "mydir/", "another_dir/"]
      assertTypedGlobWithDirMark tmpDir (assertAreEqualAndReturnFirst (patternStrict "*") [PatternSegmentNonWF.oneStar]) expected

    it "GlobWithBraces" do withinTempDirTree (tree! { "config.json", "config.yaml", "config.txt", "data.json" }) fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "config.{json,yaml}") [PatternSegmentNonWF.regex (Regex.parse! "^config\\.(json|yaml)$")]) #["config.json", "config.yaml"]

    it "NoMatchesWithoutNoCheck" do withinTempDirTree (tree! {}) fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "nonexistent.txt") [PatternSegmentNonWF.lit (nes!"nonexistent.txt")]) #[]

end
