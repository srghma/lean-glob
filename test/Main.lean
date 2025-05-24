import Glob
import Init.System.IO
import Lean.Data.RBTree
import Lean
import Lean.Data.RBMap
import Std.Data.HashSet
import Lean.Data.RBTree
import Init.System.IO
import Lean.Elab.Term
import Lean.Parser.Term
import Init.Data.Repr

open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)

/-!
## Test Suite for System.Glob FFI

This test suite creates isolated temporary directories for each test,
creates files within them, runs glob operations, and asserts the results.
-/

-- Helper for comparing arrays of strings, ignoring order
def Array.sortedEq (arr1 arr2 : Array String) : Bool :=
  arr1.insertionSort == arr2.insertionSort

-- Assertion helpers
def assertEq (name : String) (expected actual : Array String) : IO Unit := do
  unless actual.sortedEq expected do
    IO.println s!"❌ {name} failed: Expected {reprStr expected}, got {reprStr actual}"
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertBool (name : String) (expected actual : Bool) : IO Unit := do
  unless actual == expected do
    IO.println s!"❌ {name} failed: Expected {expected}, got {actual}"
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertIsNotEmpty (name : String) (actual : Array String) : IO Unit := do
  unless !actual.isEmpty do
    IO.println s!"❌ {name} failed: Expected non-empty array, got empty."
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertIsEmpty (name : String) (actual : Array String) : IO Unit := do
  unless actual.isEmpty do
    IO.println s!"❌ {name} failed: Expected empty array, got {reprStr actual}."
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def assertThrows (name : String) (ioAction : IO Unit) : IO Unit := do
  let result ← try
    ioAction
    pure none
  catch e =>
    IO.println s!"✅ {name} caught expected error: {e}"
    pure (some e)
  unless result.isSome do
    IO.println s!"❌ {name} failed: Expected an error, but no error was thrown."
    throw <| IO.Error.userError s!"Assertion failed: {name}"

def runTests (tests : Array (String × (FilePath → IO Unit))) : IO Unit := do
  let mut successCount := 0
  let totalCount := tests.size
  for (name, testFn) in tests do
    IO.println s!"\n--- Running Test: {name} ---"
    let originalCwd ← IO.currentDir
    try
      -- Execute the test within a temporary directory
      withTempDir (fun tmpDir => do
        IO.println s!"⏰ Running {name} in temporary directory: {tmpDir}"
        IO.Process.setCurrentDir tmpDir
        testFn tmpDir
        IO.Process.setCurrentDir originalCwd)
      IO.println s!"✅ {name} passed."
      successCount := successCount + 1
    catch e =>
      IO.println s!"❌ {name} failed with error: {e}"
      IO.Process.setCurrentDir originalCwd
  IO.println s!"\n--- Test Summary ---"
  IO.println s!"Total tests: {totalCount}, Passed: {successCount}, Failed: {totalCount - successCount}"
  unless successCount == totalCount do
    throw <| IO.Error.userError "Some tests failed!"

def assertGlob (pattern : Pattern) (expected : ?a) : IO Unit :=
  assertEq (Pattern.toString pattern) expected (← glob (← IO.Process.setCurrentDir) pattern)

def main : IO Unit :=
  runTests #[
    ("FindRecursive", fun (currentTmpDir : FilePath) => do -- TODO: this is a limitation of glob-posix, no support of recursion
      writeFile "foo.txt" "content"
      createDir "subdir"
      writeFile "subdir/bar.txt" "content"
      writeFile "subdir/foo.txt" "content"
      createDir "subdir/another_subdir"
      writeFile "subdir/another_subdir/bar.txt" "content"
      writeFile "subdir/another_subdir/foo.txt" "content"
      assertGlob nel![PatternSegment.doubleStar, nes!"foo.txt"] #["foo.txt", "subdir/foo.txt", "subdir/another_subdir/foo.txt"]
      assertGlob nel![nes!"foo.txt"]] #["foo.txt"]
      assertGlob nel![PatternSegment.oneStar, nes!"foo.txt"] #["subdir/foo.txt"]
    ]
    -- ("BasicWildcard", fun (_tmpDir : FilePath) => do
    --   writeFile "file1.txt" "content"
    --   writeFile "file2.txt" "content"
    --   writeFile "image.png" "content"
    --   createDir "subdir"
    --   writeFile "subdir/file3.txt" "content"
    --   createDir "empty_dir"

    --   let results ← glob "*.txt"
    --   assertEq "Basic wildcard *.txt" #["file1.txt", "file2.txt"] results

    --   let allFiles ← glob "*"
    --   assertEq "All files *" #["file1.txt", "file2.txt", "image.png", "empty_dir", "subdir"] allFiles),
    -- ("QuestionMark", fun (_tmpDir : FilePath) => do
    --   writeFile "doc1" "content"
    --   writeFile "doc2" "content"
    --   writeFile "doc_long" "content"

    --   let results ← glob "doc?"
    --   assertEq "Question mark doc?" #["doc1", "doc2"] results),
    -- ("CharacterClass", fun (_tmpDir : FilePath) => do
    --   writeFile "apple" "content"
    --   writeFile "apricot" "content"
    --   writeFile "banana" "content"
    --   assertEq "Character class a[p-r]*" #["apple", "apricot"] (← glob "a[p-r]*")),
    -- ("GlobWithDirMark", fun (_tmpDir : FilePath) => do
    --   writeFile "file.txt" "content"
    --   createDir "mydir"
    --   createDir "another_dir"
    --   let expected := #["file.txt", "mydir/", "another_dir/"]
    --   assertEq "globWithDirMark *" expected (← globWithDirMark "*")),
    -- ("GlobUnsorted", fun (_tmpDir : FilePath) => do
    --   writeFile "c.txt" "c"
    --   writeFile "a.txt" "a"
    --   writeFile "b.txt" "b"
    --   -- We can't assert a specific order, just that all are present and count is correct
    --   assertEq "globUnsorted *.txt" #["a.txt", "b.txt", "c.txt"] (← globUnsorted "*.txt")),
    -- ("CheckPattern", fun (_tmpDir : FilePath) => do
    --   writeFile "existing.txt" "content"
    --   writeFile "another.md" "content"
    --   assertBool "checkPattern *.txt (true)" true (← checkPattern "*.txt")
    --   assertBool "checkPattern *.xyz (false)" false (← checkPattern "*.xyz")
    --   assertBool "checkPattern existing.txt (true)" true (← checkPattern "existing.txt")
    --   assertBool "checkPattern non_existing.txt (false)" false (← checkPattern "non_existing.txt")),
    -- ("GlobMany", fun (_tmpDir : FilePath) => do
    --   writeFile "file.txt" "content"
    --   writeFile "doc.md" "content"
    --   writeFile "image.jpg" "content"
    --   writeFile "data.csv" "content"
    --   assertEq "globMany multiple extensions" #["file.txt", "doc.md", "data.csv"] (← globMany #["*.txt", "*.md", "*.csv"])
    --   assertEq "globMany mixed (some match, some no match)" #["file.txt"] (← globMany #["*.xyz", "*.txt"])
    --   assertIsEmpty "globMany all no match" (← globMany #["*.xyz", "*.abc"])),
    -- ("GlobWithBraces", fun (_tmpDir : FilePath) => do
    --   writeFile "config.json" "content"
    --   writeFile "config.yaml" "content"
    --   writeFile "config.txt" "content"
    --   writeFile "data.json" "content"
    --   assertEq "globWithBraces config.{json,yaml}" #["config.json", "config.yaml"] (← globWithBraces "config.{json,yaml}")),
    -- ("GlobWithTilde", fun (_tmpDir : FilePath) => do
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
    -- ("GlobDirsOnly", fun (tmpDir : FilePath) => do
    --   writeFile "file.txt" "content"
    --   createDir "dir1"
    --   createDir "dir2"
    --   writeFile (tmpDir / "dir1" / "nested_file.txt") "content"
    --   assertEq "globDirsOnly *" #["dir1/", "dir2/"] (← globDirsOnly "*")),
    -- ("GlobSafe", fun (_tmpDir : FilePath) => do
    --   writeFile "present.txt" "content"
    --   assertEq "globSafe (match)" #["present.txt"] (← globSafe "*.txt")
    --   assertEq "globSafe (no match, nocheck)" #["nonexistent.*"] (← globSafe "nonexistent.*")
    --   assertEq "globSafe (literal no match, nocheck)" #["definitely_not_here.md"] (← globSafe "definitely_not_here.md")),
    -- ("FindByExtension", fun (_tmpDir : FilePath) => do
    --   writeFile "a.lean" "content"
    --   writeFile "b.md" "content"
    --   writeFile "c.lean" "content"
    --   assertEq "findByExtension lean" #["a.lean", "c.lean"] (← findByExtension "lean")
    --   assertIsEmpty "findByExtension xyz (empty)" (← findByExtension "xyz")),
    -- ("FindByExtensions", fun (_tmpDir : FilePath) => do
    --   writeFile "a.lean" "content"
    --   writeFile "b.md" "content"
    --   writeFile "c.txt" "content"
    --   writeFile "d.json" "content"
    --   assertEq "findByExtensions lean, txt" #["a.lean", "c.txt"] (← findByExtensions #["lean", "txt"])
    --   assertIsEmpty "findByExtensions xyz, abc (empty)" (← findByExtensions #["xyz", "abc"])),
    -- ("FindDirectories", fun (tmpDir : FilePath) => do
    --   writeFile "file.txt" "content"
    --   createDir "dir1"
    --   createDir "dir2"
    --   writeFile (tmpDir / "dir1" / "nested.txt") "content"
    --   assertEq "findDirectories" #["dir1/", "dir2/"] (← findDirectories)),
    -- ("NoMatchesWithoutNoCheck", fun (_tmpDir : FilePath) => do
    --   assertIsEmpty "No matches without nocheck" (← glob "*.nonexistent")),
    -- ("TestErrFlag", fun (tmpDir : FilePath) => do
    --   -- This test remains limited due to portability of permissions.
    --   -- It primarily ensures the flag passes and doesn't crash the FFI.
    --   let restrictedDir := tmpDir / "restricted"
    --   createDir restrictedDir
    --   -- One *could* attempt `IO.Process.runCommand` for `chmod` but it's not portable
    --   -- across OSes or always reliable for testing specific error conditions.
    --   let results ← glob (restrictedDir / "*").toString { GlobFlags.default with err := true }
    --   IO.println s!"TestErrFlag: Results: {results}"
    -- )
    /- ] -/
