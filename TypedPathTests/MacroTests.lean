import TypedPath.PosixPath

open Posix

-- --- Defaults (derived from string) ---
def testAbsDir : PosixPath false .Abs .Dir false := posixPath! "/foo/bar/"
def testAbsFile : PosixPath false .Abs .File false := posixPath! "/foo/bar"
def testRelDir : PosixPath false .Rel .Dir false := posixPath! "foo/bar/"
def testRelFile : PosixPath false .Rel .File false := posixPath! "foo/bar"
def testParent : PosixPath true .Rel .File false := posixPath! "../foo/bar"
def testCwd1 : PosixPath false .Rel .File true := posixPath! "."
def testCwd2 : PosixPath false .Rel .Dir true := posixPath! "./"

-- --- Variants for Absolute Directory (/foo/bar/) ---
def absDir_tt : PosixPath true .Abs .Dir true := posixPath! (allowParents := true) (allowCwd := true) "/foo/bar/"
def absDir_tf : PosixPath true .Abs .Dir false := posixPath! (allowParents := true) (allowCwd := false) "/foo/bar/"
def absDir_ft : PosixPath false .Abs .Dir true := posixPath! (allowParents := false) (allowCwd := true) "/foo/bar/"
def absDir_ff : PosixPath false .Abs .Dir false := posixPath! (allowParents := false) (allowCwd := false) "/foo/bar/"

-- --- Variants for Absolute File (/foo/bar) ---
def absFile_tt : PosixPath true .Abs .File true := posixPath! (allowParents := true) (allowCwd := true) "/foo/bar"
def absFile_tf : PosixPath true .Abs .File false := posixPath! (allowParents := true) (allowCwd := false) "/foo/bar"
def absFile_ft : PosixPath false .Abs .File true := posixPath! (allowParents := false) (allowCwd := true) "/foo/bar"
def absFile_ff : PosixPath false .Abs .File false := posixPath! (allowParents := false) (allowCwd := false) "/foo/bar"

-- --- Variants for Relative Directory (foo/bar/) ---
def relDir_tt : PosixPath true .Rel .Dir true := posixPath! (allowParents := true) (allowCwd := true) "foo/bar/"
def relDir_tf : PosixPath true .Rel .Dir false := posixPath! (allowParents := true) (allowCwd := false) "foo/bar/"
def relDir_ft : PosixPath false .Rel .Dir true := posixPath! (allowParents := false) (allowCwd := true) "foo/bar/"
def relDir_ff : PosixPath false .Rel .Dir false := posixPath! (allowParents := false) (allowCwd := false) "foo/bar/"

-- --- Variants for Relative File (foo/bar) ---
def relFile_tt : PosixPath true .Rel .File true := posixPath! (allowParents := true) (allowCwd := true) "foo/bar"
def relFile_tf : PosixPath true .Rel .File false := posixPath! (allowParents := true) (allowCwd := false) "foo/bar"
def relFile_ft : PosixPath false .Rel .File true := posixPath! (allowParents := false) (allowCwd := true) "foo/bar"
def relFile_ff : PosixPath false .Rel .File false := posixPath! (allowParents := false) (allowCwd := false) "foo/bar"

-- --- Variants for Parent Directory (../foo/bar) ---
-- Note: allowParents MUST be true since the path contains '..'
def parent_tt : PosixPath true .Rel .File true := posixPath! (allowParents := true) (allowCwd := true) "../foo/bar"
def parent_tf : PosixPath true .Rel .File false := posixPath! (allowParents := true) (allowCwd := false) "../foo/bar"

-- --- Variants for Cwd (.) ---
-- Note: allowCwd MUST be true since the path is '.'
def cwd_tt : PosixPath true .Rel .File true := posixPath! (allowParents := true) (allowCwd := true) "."
def cwd_ft : PosixPath false .Rel .File true := posixPath! (allowParents := false) (allowCwd := true) "."

-- --- Variants for Cwd (./) ---
def cwd_dir_tt : PosixPath true .Rel .Dir true := posixPath! (allowParents := true) (allowCwd := true) "./"
def cwd_dir_ft : PosixPath false .Rel .Dir true := posixPath! (allowParents := false) (allowCwd := true) "./"

-- Ensure we can mix the order of named arguments
def out_of_order_tt : PosixPath true .Abs .Dir true := posixPath! (allowCwd := true) (allowParents := true) "/foo/bar/"
