module
import TypedPath.PosixPath
meta import TypedPath.PosixPath

namespace Posix.Tests
open Posix


-- --- Component-level: NAME_MAX -----------------------------------------

#guard decide (parsePathComponent "var" = some (.normal (ValidComponent.mk! "var")))
#guard decide (parsePathComponent "." = some .current)
#guard decide (parsePathComponent ".." = some .parent)
#guard decide (parsePathComponent ("".pushn 'a' NAME_MAX) ≠ none)        -- exactly 255 bytes: OK
#guard decide (parsePathComponent ("".pushn 'a' (NAME_MAX + 1)) = none)  -- 256 bytes: rejected

-- --- Raw parsing (no PATH_MAX check yet) -------------------------------

#guard decide (parsePosixPathRaw "/var/log/syslog" =
  some (.absolute [.normal (ValidComponent.mk! "var"), .normal (ValidComponent.mk! "log"), .normal (ValidComponent.mk! "syslog")]))
#guard decide (parsePosixPathRaw "config.json" = some (.relative [.normal (ValidComponent.mk! "config.json")]))
#guard decide (parsePosixPathRaw "./scripts/deploy.sh" =
  some (.relative [.current, .normal (ValidComponent.mk! "scripts"), .normal (ValidComponent.mk! "deploy.sh")]))
#guard decide (parsePosixPathRaw "../logs/error.log" =
  some (.relative [.parent, .normal (ValidComponent.mk! "logs"), .normal (ValidComponent.mk! "error.log")]))
#guard decide (parsePosixPathRaw ".." = some (.relative [.parent]))
#guard decide (parsePosixPathRaw "../" = some (.relative [.parent]))
#guard decide (parsePosixPathRaw ".../" = some (.relative [.normal (ValidComponent.mk! "...")]))
#guard decide (parsePosixPathRaw "." = some (.relative [.current]))
#guard decide (parsePosixPathRaw "./" = some (.relative [.current]))
#guard decide (parsePosixPathRaw "" = none)

-- A component that's individually too long fails the *raw* parse too,
-- since `parsePathComponent` already enforces `NAME_MAX`.
#guard decide (parsePosixPathRaw ("/" ++ "".pushn 'a' 300) = none)

-- --- Fully validated parsing: PATH_MAX -------------------------------

#guard decide ((parsePosixPath "/var/log/syslog").map (·.path) =
  some (.absolute [.normal (ValidComponent.mk! "var"), .normal (ValidComponent.mk! "log"), .normal (ValidComponent.mk! "syslog")]))
#guard decide ((parsePosixPath "/var/log/syslog").map (·.path.toString) =
  some "/var/log/syslog")

-- 18 segments of 250 bytes + 17 separators = 4517 bytes > PATH_MAX (4095),
-- even though every individual segment is well under NAME_MAX (255).
def longSeg : String := "".pushn 'a' 250
def tooLongPath : String := "/" ++ String.intercalate "/" (List.replicate 18 longSeg)

#guard decide (parsePosixPathRaw tooLongPath ≠ none)  -- every component is individually fine
#guard decide (parsePosixPath tooLongPath = none)      -- but the whole path is too long

end Posix.Tests
