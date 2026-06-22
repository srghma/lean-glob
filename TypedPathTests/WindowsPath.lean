module
import TypedPath.WindowsPath
meta import TypedPath.WindowsPath

namespace Windows.Tests
open Windows

-- Test-only convenience constructors (see the note in PosixPath.lean).
instance : Inhabited ValidDriveChar :=
  ⟨{ toChar := 'A' }⟩
instance : Inhabited ValidComponent :=
  ⟨{ toString := "x" }⟩

def dc! (c : Char) : ValidDriveChar := (ValidDriveChar.mk? c).getD default
def wnc! (s : String) : PathComponent := .normal ((ValidComponent.mk? s).getD default)

-- --- Component-level: SEGMENT_MAX --------------------------------------

#guard decide (parsePathComponent ("".pushn 'a' SEGMENT_MAX) ≠ none)        -- 255 units: OK
#guard decide (parsePathComponent ("".pushn 'a' (SEGMENT_MAX + 1)) = none)  -- 256 units: rejected

-- --- Raw parsing (no whole-path length check yet) ----------------------

#guard decide (parseWindowsPathRaw r"C:\Windows\System32\cmd.exe" =
  some ⟨.driveAbsolute (dc! 'C'), [wnc! "Windows", wnc! "System32", wnc! "cmd.exe"]⟩)
#guard decide (parseWindowsPathRaw r"C:\Windows/System32\cmd.exe" =
  some ⟨.driveAbsolute (dc! 'C'), [wnc! "Windows", wnc! "System32", wnc! "cmd.exe"]⟩)
#guard decide (parseWindowsPathRaw r"\\Server01\Shared\Reports" =
  some ⟨.unc "Server01" "Shared", [wnc! "Reports"]⟩)
#guard decide (parseWindowsPathRaw r"\\?\C:\VeryLongPath\file.txt" =
  some ⟨.verbatimDisk (dc! 'C'), [wnc! "VeryLongPath", wnc! "file.txt"]⟩)
#guard decide (parseWindowsPathRaw r"\\?\UNC\Server01\Shared\file.txt" =
  some ⟨.verbatimUnc "Server01" "Shared", [wnc! "file.txt"]⟩)
#guard decide (parseWindowsPathRaw r"settings.ini" = some ⟨.relative, [wnc! "settings.ini"]⟩)
#guard decide (parseWindowsPathRaw r"\Users\John\Documents" =
  some ⟨.currentDriveAbsolute, [wnc! "Users", wnc! "John", wnc! "Documents"]⟩)
#guard decide (parseWindowsPathRaw r"D:Documents\budget.xlsx" =
  some ⟨.driveRelative (dc! 'D'), [wnc! "Documents", wnc! "budget.xlsx"]⟩)

-- lower-case drive letters canonicalise to upper-case
#guard decide (parseWindowsPathRaw r"c:\Windows" = parseWindowsPathRaw r"C:\Windows")

-- consecutive / mixed separators collapse
#guard decide (parseWindowsPathRaw r"C:\\\\\Windows\\System32\\cmd.exe" =
  parseWindowsPathRaw r"C:\Windows\System32\cmd.exe")
#guard decide (parseWindowsPathRaw r"C:\/\/\/Windows\System32\cmd.exe" =
  parseWindowsPathRaw r"C:\Windows\System32\cmd.exe")

-- --- Fully validated parsing: prefix-dependent whole-path limit --------

def winLongSeg : String := "".pushn 'a' 250

-- "C:\" + two 250-char segments + 1 separator = 504 units > LEGACY_PATH_MAX (259)
def legacyTooLong : String :=
  "C:\\" ++ String.intercalate "\\" (List.replicate 2 winLongSeg)

#guard decide (parseWindowsPathRaw legacyTooLong ≠ none)   -- each segment is fine on its own
#guard decide (parseWindowsPath legacyTooLong = none)       -- but exceeds the legacy 259 limit

-- same content, but with the verbatim prefix: well under VERBATIM_PATH_MAX (32767)
def verbatimOk : String :=
  "\\\\?\\C:\\" ++ String.intercalate "\\" (List.replicate 2 winLongSeg)

#guard decide ((parseWindowsPath verbatimOk).isSome)

end Windows.Tests
