module
public import GlobTest.Spec.RunTests
public import GlobTest.Spec.Assert
public import Glob
public import Glob.WF.Types
public import Glob.WF.Elab
public import NonEmpty.List
public import NonEmpty.String
public import GlobTest.FileFinder



@[expose] public section

open System (FilePath)
open IO.FS
open NonEmpty.List
open NonEmpty.String


def runGlobRealTests : IO Unit := do
  runTests #[
    ("FindRecursive", withinTempDir do
      writeFile "foo.txt" "content"
      createDir "subdir"
      writeFile "subdir/bar.txt" "content"
      writeFile "subdir/foo.txt" "content"
      createDir "subdir/another_subdir"
      writeFile "subdir/another_subdir/bar.txt" "content"
      writeFile "subdir/another_subdir/foo.txt" "content"
      assertGlob (assertAreEqualAndReturnFirst (patternStrict "**/foo.txt") ![PatternSegmentNonWF.doubleStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt", "subdir/foo.txt", "subdir/another_subdir/foo.txt"]
      assertGlob (assertAreEqualAndReturnFirst (patternStrict "foo.txt") ![PatternSegmentNonWF.lit (nes!"foo.txt")]) #["foo.txt"]
      assertGlob (assertAreEqualAndReturnFirst (patternStrict "*/foo.txt") ![PatternSegmentNonWF.oneStar, PatternSegmentNonWF.lit (nes!"foo.txt")]) #["subdir/foo.txt"]
    ),
    ("BasicWildcard", withinTempDir do
      writeFile "file1.txt" "content"
      writeFile "file2.txt" "content"
      writeFile "image.png" "content"
      createDir "subdir"
      writeFile "subdir/file3.txt" "content"
      createDir "empty_dir"

      assertGlob (assertAreEqualAndReturnFirst (patternStrict "*") ![PatternSegmentNonWF.oneStar]) #["empty_dir", "file1.txt", "file2.txt", "image.png", "subdir"]),
    ("QuestionMark", withinTempDir do
      writeFile "doc1" "content"
      writeFile "doc2" "content"
      writeFile "doc_long" "content"

      assertGlob (assertAreEqualAndReturnFirst (patternStrict "doc?") ![PatternSegmentNonWF.regex (Regex.parse! "^doc.$")]) #["doc1", "doc2"]),
    ("CharacterClass", withinTempDir do
      writeFile "apple" "content"
      writeFile "apricot" "content"
      writeFile "banana" "content"
      assertGlob (assertAreEqualAndReturnFirst (patternStrict "a[p-r]*") ![PatternSegmentNonWF.regex (Regex.parse! "^a[p-r].*$")]) #["apple", "apricot"]),
    ("GlobWithDirMark", withinTempDir do
      writeFile "file.txt" "content"
      createDir "mydir"
      createDir "another_dir"
      let expected := #["file.txt", "mydir/", "another_dir/"]
      assertEq "globWithDirMark *" expected (← globWithDirMark "*")),
    -- ("GlobUnsorted", do
    --   let _tmpDir ← IO.currentDir
    --   writeFile "c.txt" "c"
    --   writeFile "a.txt" "a"
    --   writeFile "b.txt" "b"
    --   -- We can't assert a specific order, just that all are present and count is correct
    --   assertEq "globUnsorted *.txt" #["a.txt", "b.txt", "c.txt"] (← globUnsorted "*.txt")),
    -- ("CheckPattern", do
    --   let _tmpDir ← IO.currentDir
    --   writeFile "existing.txt" "content"
    --   writeFile "another.md" "content"
    --   assertBool "checkPattern *.txt (true)" true (← checkPattern "*.txt")
    --   assertBool "checkPattern *.xyz (false)" false (← checkPattern "*.xyz")
    --   assertBool "checkPattern existing.txt (true)" true (← checkPattern "existing.txt")
    --   assertBool "checkPattern non_existing.txt (false)" false (← checkPattern "non_existing.txt")),
    ("GlobMany", withinTempDir do
      writeFile "file.txt" "content"
      writeFile "doc.md" "content"
      writeFile "image.jpg" "content"
      writeFile "data.csv" "content"
      assertGlobMany ![![PatternSegmentNonWF.lit (nes!"file.txt")], ![PatternSegmentNonWF.lit (nes!"doc.md")], ![PatternSegmentNonWF.lit (nes!"data.csv")]] #["data.csv", "doc.md", "file.txt"]
      assertGlobMany ![![PatternSegmentNonWF.lit (nes!"nonexistent.xyz")], ![PatternSegmentNonWF.lit (nes!"file.txt")]] #["file.txt"]
      assertGlobMany ![![PatternSegmentNonWF.lit (nes!"nonexistent.xyz")], ![PatternSegmentNonWF.lit (nes!"nonexistent.abc")]] #[]),
    ("GlobWithBraces", withinTempDir do
      writeFile "config.json" "content"
      writeFile "config.yaml" "content"
      writeFile "config.txt" "content"
      writeFile "data.json" "content"
      assertGlob (assertAreEqualAndReturnFirst (patternStrict "config.{json,yaml}") ![PatternSegmentNonWF.regex (Regex.parse! "^config\\.(json|yaml)$")]) #["config.json", "config.yaml"]),
    -- ("GlobWithTilde", do
    --   let _tmpDir ← IO.currentDir
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
    --     IO.println s!"Found {results.size} files with tilde expansion, e.g., {results[0]!}"),
    -- ("GlobDirsOnly", do
    --   let tmpDir ← IO.currentDir
    --   writeFile "file.txt" "content"
    --   createDir "dir1"
    --   createDir "dir2"
    --   writeFile (tmpDir / "dir1" / "nested_file.txt") "content"
    --   assertEq "globDirsOnly *" #["dir1/", "dir2/"] (← globDirsOnly "*")),
    -- ("GlobSafe", do
    --   let _tmpDir ← IO.currentDir
    --   writeFile "present.txt" "content"
    --   assertEq "globSafe (match)" #["present.txt"] (← globSafe "*.txt")
    --   assertEq "globSafe (no match, nocheck)" #["nonexistent.*"] (← globSafe "nonexistent.*")
    --   assertEq "globSafe (literal no match, nocheck)" #["definitely_not_here.md"] (← globSafe "definitely_not_here.md")),
    ("FindByExtension", withinTempDir do
      writeFile "a.lean" "content"
      writeFile "b.md" "content"
      writeFile "c.lean" "content"
      assertEq "findByExtension lean" #["a.lean", "c.lean"] (← findByExtension "lean")
      assertIsEmpty "findByExtension xyz (empty)" (← findByExtension "xyz")),
    ("FindByExtensions", withinTempDir do
      writeFile "a.lean" "content"
      writeFile "b.md" "content"
      writeFile "c.txt" "content"
      writeFile "d.json" "content"
      assertEq "findByExtensions lean, txt" #["a.lean", "c.txt"] (← findByExtensions #["lean", "txt"])
      assertIsEmpty "findByExtensions xyz, abc (empty)" (← findByExtensions #["xyz", "abc"])),
    ("FindDirectories", withinTempDir do
      let tmpDir ← IO.currentDir
      writeFile "file.txt" "content"
      createDir "dir1"
      createDir "dir2"
      writeFile (tmpDir / "dir1" / "nested.txt") "content"
      assertEq "findDirectories" #["dir1/", "dir2/"] (← findDirectories)),
    ("NoMatchesWithoutNoCheck", withinTempDir do
      assertGlob (assertAreEqualAndReturnFirst (patternStrict "nonexistent.txt") ![PatternSegmentNonWF.lit (nes!"nonexistent.txt")]) #[]),
    -- ("TestErrFlag", do
    --   let tmpDir ← IO.currentDir
    --   -- This test remains limited due to portability of permissions.
    --   -- It primarily ensures the flag passes and doesn't crash the FFI.
    --   let restrictedDir := tmpDir / "restricted"
    --   createDir restrictedDir
    --   -- One *could* attempt `IO.Process.runCommand` for `chmod` but it's not portable
    --   -- across OSes or always reliable for testing specific error conditions.
    --   let results ← glob (restrictedDir / "*").toString { GlobFlags.default with err := true }
    --   IO.println s!"TestErrFlag: Results: {results}"
    -- )
  ]

end
