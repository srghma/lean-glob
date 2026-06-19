module
public import GlobTest.Spec.Core
public import GlobTest.Spec.Assert
public import Glob
public import Glob.WF.Types
public import Glob.WF.Elab
public import NonEmpty.List
public import NonEmpty.String

@[expose] public section

open System (FilePath)
open IO.FS
open NonEmpty.List
open NonEmpty.String
open GlobTest.Spec.Core
open GlobTest.Spec.Assert

/-- Real filesystem specs. Each `it` runs inside its own temp dir, so they are
safe to run in parallel. -/
def globRealSpec : Spec := do
  describe "Glob (real filesystem)" do
    it "FindRecursive" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "foo.txt") "content"
      createDir (tmpDir / "subdir")
      writeFile (tmpDir / "subdir/bar.txt") "content"
      writeFile (tmpDir / "subdir/foo.txt") "content"
      createDir (tmpDir / "subdir/another_subdir")
      writeFile (tmpDir / "subdir/another_subdir/bar.txt") "content"
      writeFile (tmpDir / "subdir/another_subdir/foo.txt") "content"
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "**/foo.txt") ![PatternSegmentNonWF.doubleStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt", "subdir/foo.txt", "subdir/another_subdir/foo.txt"]
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "foo.txt") ![PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt"]
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "*/foo.txt") ![PatternSegmentNonWF.oneStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["subdir/foo.txt"]

    it "BasicWildcard" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file1.txt") "content"
      writeFile (tmpDir / "file2.txt") "content"
      writeFile (tmpDir / "image.png") "content"
      createDir (tmpDir / "subdir")
      writeFile (tmpDir / "subdir/file3.txt") "content"
      createDir (tmpDir / "empty_dir")
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "*") ![PatternSegmentNonWF.oneStar]) #["empty_dir", "file1.txt", "file2.txt", "image.png", "subdir"]

    it "QuestionMark" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "doc1") "content"
      writeFile (tmpDir / "doc2") "content"
      writeFile (tmpDir / "doc_long") "content"
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "doc?") ![PatternSegmentNonWF.regex (Regex.parse! "^doc.$")]) #["doc1", "doc2"]

    it "CharacterClass" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "apple") "content"
      writeFile (tmpDir / "apricot") "content"
      writeFile (tmpDir / "banana") "content"
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "a[p-r]*") ![PatternSegmentNonWF.regex (Regex.parse! "^a[p-r].*$")]) #["apple", "apricot"]

    it "GlobWithDirMark" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file.txt") "content"
      createDir (tmpDir / "mydir")
      createDir (tmpDir / "another_dir")
      let expected := #["file.txt", "mydir/", "another_dir/"]
      assertEq "globWithDirMark *" expected (← globWithDirMark tmpDir (patternStrict "*"))

    it "CheckPattern" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "existing.txt") "content"
      writeFile (tmpDir / "another.md") "content"
      assertBool "checkPattern *.txt (true)" true (← checkPattern tmpDir (patternStrict "*.txt"))
      assertBool "checkPattern *.xyz (false)" false (← checkPattern tmpDir (patternStrict "*.xyz"))
      assertBool "checkPattern existing.txt (true)" true (← checkPattern tmpDir (patternStrict "existing.txt"))
      assertBool "checkPattern non_existing.txt (false)" false (← checkPattern tmpDir (patternStrict "non_existing.txt"))

    it "GlobMany" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file.txt") "content"
      writeFile (tmpDir / "doc.md") "content"
      writeFile (tmpDir / "image.jpg") "content"
      writeFile (tmpDir / "data.csv") "content"
      assertGlobMany tmpDir ![(assertAreEqualAndReturnFirst (patternStrict "file.txt") ![PatternSegmentNonWF.lit (nes!"file.txt")]),(assertAreEqualAndReturnFirst (patternStrict "doc.md") ![PatternSegmentNonWF.lit (nes!"doc.md")]),(assertAreEqualAndReturnFirst (patternStrict "data.csv") ![PatternSegmentNonWF.lit (nes!"data.csv")])] #["data.csv", "doc.md", "file.txt"]
      assertGlobMany tmpDir ![(assertAreEqualAndReturnFirst (patternStrict "nonexistent.xyz") ![PatternSegmentNonWF.lit (nes!"nonexistent.xyz")]),(assertAreEqualAndReturnFirst (patternStrict "file.txt") ![PatternSegmentNonWF.lit (nes!"file.txt")])] #["file.txt"]
      assertGlobMany tmpDir ![(assertAreEqualAndReturnFirst (patternStrict "nonexistent.xyz") ![PatternSegmentNonWF.lit (nes!"nonexistent.xyz")]),(assertAreEqualAndReturnFirst (patternStrict "nonexistent.abc") ![PatternSegmentNonWF.lit (nes!"nonexistent.abc")])] #[]

    it "GlobWithBraces" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "config.json") "content"
      writeFile (tmpDir / "config.yaml") "content"
      writeFile (tmpDir / "config.txt") "content"
      writeFile (tmpDir / "data.json") "content"
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "config.{json,yaml}") ![PatternSegmentNonWF.regex (Regex.parse! "^config\\.(json|yaml)$")]) #["config.json", "config.yaml"]

    -- it "GlobWithTilde" do withinTempDir fun tmpDir => do
    --   -- Tilde expansion is highly environment-dependent. This test primarily checks
    --   -- that the flag is passed and doesn't cause a crash. A true functional test
    --   -- would require setting up a controlled home directory, which is non-trivial.
    --   let homeDirFile := "~/.profile"
    --   let results ← globWithTilde homeDirFile
    --   if results.isEmpty then
    --     IO.println s!"Warning: {homeDirFile} not found or tilde expansion failed. (This might be normal depending on environment/config)"
    --     pure ()
    --   else
    --     assertIsNotEmpty "globWithTilde ~/" results

    it "GlobDirsOnly" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file.txt") "content"
      createDir (tmpDir / "dir1")
      createDir (tmpDir / "dir2")
      writeFile (tmpDir / "dir1" / "nested_file.txt") "content"
      assertEq "globDirsOnly *" #["dir1/", "dir2/"] (← globDirsOnly tmpDir (assertAreEqualAndReturnFirst (patternStrict "*") ![PatternSegmentNonWF.oneStar]))

    it "FindByExtension" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "a.lean") "content"
      writeFile (tmpDir / "b.md") "content"
      writeFile (tmpDir / "c.lean") "content"
      assertEq "findByExtension lean" #["a.lean", "c.lean"] (← findByExtension tmpDir "lean")
      assertIsEmpty "findByExtension xyz (empty)" (← findByExtension tmpDir "xyz")

    it "FindByExtensions" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "a.lean") "content"
      writeFile (tmpDir / "b.md") "content"
      writeFile (tmpDir / "c.txt") "content"
      writeFile (tmpDir / "d.json") "content"
      assertEq "findByExtensions lean, txt" #["a.lean", "c.txt"] (← findByExtensions tmpDir #["lean", "txt"])
      assertIsEmpty "findByExtensions xyz, abc (empty)" (← findByExtensions tmpDir #["xyz", "abc"])

    it "FindDirectories" do withinTempDir fun tmpDir => do
      writeFile (tmpDir / "file.txt") "content"
      createDir (tmpDir / "dir1")
      createDir (tmpDir / "dir2")
      writeFile (tmpDir / "dir1" / "nested.txt") "content"
      assertEq "findDirectories tmpDir" #["dir1/", "dir2/"] (← findDirectories tmpDir)

    it "NoMatchesWithoutNoCheck" do withinTempDir fun tmpDir => do
      assertGlob tmpDir (assertAreEqualAndReturnFirst (patternStrict "nonexistent.txt") ![PatternSegmentNonWF.lit (nes!"nonexistent.txt")]) #[]

    if !System.Platform.isWindows then
      it "TestRestrictedFolder" do withinTempDir fun tmpDir => do
        let restrictedDir := tmpDir / "restricted"
        createDir restrictedDir
        writeFile (restrictedDir / "hidden.txt") "secret"

        let chmodRes ← try
          let _ ← IO.Process.run { cmd := "chmod", args := #["000", restrictedDir.toString] }
          pure true
        catch _ => pure false

        if chmodRes then
          try
            let results ← globFS tmpDir (assertAreEqualAndReturnFirst (patternStrict "restricted/*") ![PatternSegmentNonWF.lit (nes!"restricted"), PatternSegmentNonWF.oneStar])
            assertEq "globFS on restricted" #[] results
          finally
            -- Restore permissions so cleanup works
            let _ ← try IO.Process.run { cmd := "chmod", args := #["755", restrictedDir.toString] } catch _ => pure ""
