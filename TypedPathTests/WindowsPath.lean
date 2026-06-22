module
import TypedPath.WindowsPath
meta import TypedPath.WindowsPath

namespace Windows.Tests
open Windows

-- --- Component-level: SEGMENT_MAX --------------------------------------

#guard decide (parsePathComponent ("".pushn 'a' SEGMENT_MAX) ≠ none)        -- 255 units: OK
#guard decide (parsePathComponent ("".pushn 'a' (SEGMENT_MAX + 1)) = none)  -- 256 units: rejected

-- Server and share name limit tests
#guard decide (parseWindowsPathRaw ("\\\\" ++ "".pushn 'a' SERVER_MAX ++ "\\Shared\\Reports") ≠ none)
#guard decide (parseWindowsPathRaw ("\\\\" ++ "".pushn 'a' (SERVER_MAX + 1) ++ "\\Shared\\Reports") = none)
#guard decide (parseWindowsPathRaw ("\\\\Server01\\" ++ "".pushn 'a' SHARE_MAX ++ "\\Reports") ≠ none)
#guard decide (parseWindowsPathRaw ("\\\\Server01\\" ++ "".pushn 'a' (SHARE_MAX + 1) ++ "\\Reports") = none)

-- --- Raw parsing (no whole-path length check yet) ----------------------

#guard decide (parseWindowsPathRaw r"C:\Windows\System32\cmd.exe" =
  some ⟨.driveAbsolute (ValidDriveChar.mk! 'C'), [.normal (ValidComponent.mk! "Windows"), .normal (ValidComponent.mk! "System32"), .normal (ValidComponent.mk! "cmd.exe")]⟩)
#guard decide (parseWindowsPathRaw r"C:\Windows/System32\cmd.exe" =
  some ⟨.driveAbsolute (ValidDriveChar.mk! 'C'), [.normal (ValidComponent.mk! "Windows"), .normal (ValidComponent.mk! "System32"), .normal (ValidComponent.mk! "cmd.exe")]⟩)
#guard decide (parseWindowsPathRaw r"\\Server01\Shared\Reports" =
  some ⟨.unc (ValidServer.mk! "Server01") (ValidShare.mk! "Shared"), [.normal (ValidComponent.mk! "Reports")]⟩)
#guard decide (parseWindowsPathRaw r"\\?\C:\VeryLongPath\file.txt" =
  some ⟨.verbatimDisk (ValidDriveChar.mk! 'C'), [.normal (ValidComponent.mk! "VeryLongPath"), .normal (ValidComponent.mk! "file.txt")]⟩)
#guard decide (parseWindowsPathRaw r"\\?\UNC\Server01\Shared\file.txt" =
  some ⟨.verbatimUnc (ValidServer.mk! "Server01") (ValidShare.mk! "Shared"), [.normal (ValidComponent.mk! "file.txt")]⟩)
#guard decide (parseWindowsPathRaw r"settings.ini" = some ⟨.relative, [.normal (ValidComponent.mk! "settings.ini")]⟩)
#guard decide (parseWindowsPathRaw r"\Users\John\Documents" =
  some ⟨.currentDriveAbsolute, [.normal (ValidComponent.mk! "Users"), .normal (ValidComponent.mk! "John"), .normal (ValidComponent.mk! "Documents")]⟩)
#guard decide (parseWindowsPathRaw r"D:Documents\budget.xlsx" =
  some ⟨.driveRelative (ValidDriveChar.mk! 'D'), [.normal (ValidComponent.mk! "Documents"), .normal (ValidComponent.mk! "budget.xlsx")]⟩)

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
