module
public import Init.System.IO
public import Init.System.FilePath
public import LSpec
public import GlobTest.Spec.Core
public import GlobTest.Spec.Assert
public import TypedGlob.IO

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
    it "FindRecursive" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "foo.txt") "content"
      createDir (tmpDir / "subdir")
      writeFile (tmpDir / "subdir/bar.txt") "content"
      writeFile (tmpDir / "subdir/foo.txt") "content"
      createDir (tmpDir / "subdir/another_subdir")
      writeFile (tmpDir / "subdir/another_subdir/bar.txt") "content"
      writeFile (tmpDir / "subdir/another_subdir/foo.txt") "content"
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "**/foo.txt") [PatternSegmentNonWF.doubleStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt", "subdir/foo.txt", "subdir/another_subdir/foo.txt"]
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "foo.txt") [PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt"]
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "*/foo.txt") [PatternSegmentNonWF.oneStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["subdir/foo.txt"]

    it "BasicWildcard" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file1.txt") "content"
      writeFile (tmpDir / "file2.txt") "content"
      writeFile (tmpDir / "image.png") "content"
      createDir (tmpDir / "subdir")
      writeFile (tmpDir / "subdir/file3.txt") "content"
      createDir (tmpDir / "empty_dir")
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "*") [PatternSegmentNonWF.oneStar]) #["empty_dir", "file1.txt", "file2.txt", "image.png", "subdir"]

    it "QuestionMark" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "doc1") "content"
      writeFile (tmpDir / "doc2") "content"
      writeFile (tmpDir / "doc_long") "content"
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "doc?") [PatternSegmentNonWF.regex (Regex.parse! "^doc.$")]) #["doc1", "doc2"]

    it "CharacterClass" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "apple") "content"
      writeFile (tmpDir / "apricot") "content"
      writeFile (tmpDir / "banana") "content"
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "a[p-r]*") [PatternSegmentNonWF.regex (Regex.parse! "^a[p-r].*$")]) #["apple", "apricot"]

    it "GlobWithDirMark" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file.txt") "content"
      createDir (tmpDir / "mydir")
      createDir (tmpDir / "another_dir")
      let expected := #["file.txt", "mydir/", "another_dir/"]
      assertTypedGlobWithDirMark tmpDir (assertAreEqualAndReturnFirst (patternStrict "*") [PatternSegmentNonWF.oneStar]) expected

    it "GlobWithBraces" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "config.json") "content"
      writeFile (tmpDir / "config.yaml") "content"
      writeFile (tmpDir / "config.txt") "content"
      writeFile (tmpDir / "data.json") "content"
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "config.{json,yaml}") [PatternSegmentNonWF.regex (Regex.parse! "^config\\.(json|yaml)$")]) #["config.json", "config.yaml"]

    it "NoMatchesWithoutNoCheck" do withinTempDir fun tmpDir => do
      assertTypedGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "nonexistent.txt") [PatternSegmentNonWF.lit (nes!"nonexistent.txt")]) #[]

