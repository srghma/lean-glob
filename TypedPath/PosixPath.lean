import NonEmpty.String
import TypedPath.PathCommon

/-!
# POSIX (Linux) paths

Two length limits matter on Linux:

* `NAME_MAX` — a single path component must be non-empty and at most `255`
  **bytes**. This is a byte limit, not a character limit: multi-byte UTF-8
  characters (emoji, CJK, Cyrillic, Arabic, …) eat the budget faster than
  ASCII does.
* `PATH_MAX` — the whole path, once re-serialised to a string, must be at
  most `4095` bytes of text (the kernel's 4096-byte buffer, minus the
  terminating `NUL` byte).

Both limits below are baked into the *types*: you cannot construct a
`Posix.ValidComponent` or a `Posix.ValidPath` that violates them, because the
only way to build one is through a smart constructor that checks the bound
and hands back the resulting `Nat`-inequality as a proof obligation. Since
every bound here is a concrete, decidable `Nat ≤`, that check is literally
just `Nat.decLe` doing the work — no hand-written proofs (and no `sorry`s)
were actually needed.
-/
open NonEmpty.String

namespace Posix

/-- `NAME_MAX`: maximum length of a single path component, in bytes. -/
def NAME_MAX : Nat := 255

/-- `PATH_MAX`: maximum length of a whole path, in bytes of text. This is
    `4096 - 1`: the kernel's buffer size minus the terminating `NUL` byte
    that isn't part of the text itself. -/
def PATH_MAX : Nat := 4095

/-- A path-component name that is non-empty and at most `NAME_MAX` bytes
    long. -/
structure ValidComponent extends NonEmptyString where
  len_le : toString.utf8ByteSize ≤ NAME_MAX := by decide
deriving DecidableEq

instance : ToString ValidComponent := ⟨(·.toString)⟩

/-- Smart constructor: validates non-emptiness and the `NAME_MAX` bound. -/
def ValidComponent.mk? (s : String) : Option ValidComponent :=
  if h1 : s ≠ "" then
    if h2 : s.utf8ByteSize ≤ NAME_MAX then
      some { toString := s, isNonEmpty := h1, len_le := h2 }
    else none
  else none

theorem ValidComponent.utf8ByteSize_le (c : ValidComponent) :
    c.toString.utf8ByteSize ≤ NAME_MAX := c.len_le

/-- A single component of a POSIX path. -/
inductive PathComponent where
  | current                              -- "."
  | parent                               -- ".."
  | normal (name : ValidComponent)       -- a validated file/directory name
deriving DecidableEq

def PathComponent.toString : PathComponent → String
  | .current  => "."
  | .parent   => ".."
  | .normal n => n.toString

instance : ToString PathComponent := ⟨PathComponent.toString⟩

/-- Parses a single path component. `.` and `..` are recognised specially
    (they're not subject to `NAME_MAX` — the kernel treats them as fixed
    pseudo-entries, not arbitrary names); anything else must satisfy
    `ValidComponent`, otherwise the whole parse fails. -/
def parsePathComponent (s : String) : Option PathComponent :=
  if s == "." then some .current
  else if s == ".." then some .parent
  else (ValidComponent.mk? s).map .normal

/-- A POSIX path, before the whole-path `PATH_MAX` check. -/
inductive PosixPath where
  | absolute (components : List PathComponent)
  | relative (components : List PathComponent)
deriving DecidableEq

def PosixPath.toString : PosixPath → String
  | .absolute cs => "/" ++ String.intercalate "/" (cs.map PathComponent.toString)
  | .relative cs => String.intercalate "/" (cs.map PathComponent.toString)

instance : ToString PosixPath := ⟨PosixPath.toString⟩

/-- Parses every component of a `/`-separated path, failing the whole parse
    if *any* component violates `NAME_MAX`. Doesn't yet check `PATH_MAX` —
    see `parsePosixPath` below for that. -/
def parsePosixPathRaw (s : String) : Option PosixPath :=
  if s.isEmpty then none
  else if s.startsWith "/" then
    let rest := s.toList.drop 1
    let parts := splitOnPred rest (· == '/')
    (parts.mapM parsePathComponent).map .absolute
  else
    let parts := splitOnPred s.toList (· == '/')
    (parts.mapM parsePathComponent).map .relative

/-- A `PosixPath` together with a proof that re-serialising it
    (`PosixPath.toString`) never exceeds `PATH_MAX` bytes. This is the type
    you actually want to hand around once a path has been validated. -/
structure ValidPath where
  path : PosixPath
  size_le : path.toString.utf8ByteSize ≤ PATH_MAX
deriving DecidableEq

instance : ToString ValidPath := ⟨fun vp => vp.path.toString⟩

/-- Smart constructor for `ValidPath`. Each component was already checked
    against `NAME_MAX` while parsing, so this only has to add the
    whole-path `PATH_MAX` check. -/
def PosixPath.toValid? (p : PosixPath) : Option ValidPath :=
  if h : p.toString.utf8ByteSize ≤ PATH_MAX then some ⟨p, h⟩ else none

theorem ValidPath.toString_le_PATH_MAX (vp : ValidPath) :
    vp.path.toString.utf8ByteSize ≤ PATH_MAX := vp.size_le

/-- Parse a string into a fully-validated POSIX path: every component must
    satisfy `NAME_MAX`, and the whole re-serialised path must satisfy
    `PATH_MAX`. -/
def parsePosixPath (s : String) : Option ValidPath :=
  (parsePosixPathRaw s).bind PosixPath.toValid?

end Posix

-- ======================================================================
-- Tests
-- ======================================================================

namespace Posix.Tests
open Posix

-- Test-only convenience: build a `ValidComponent` straight from a literal
-- you already know is valid, so the test data below reads almost like the
-- original file. Falls back to a dummy "x" if you ever pass it something
-- invalid — fine for tests, do not use this pattern outside of tests.
instance : Inhabited ValidComponent :=
  ⟨{ toString := "x" }⟩

def nc! (s : String) : PathComponent := .normal ((ValidComponent.mk? s).getD default)

-- --- Component-level: NAME_MAX -----------------------------------------

#guard decide (parsePathComponent "var" = some (nc! "var"))
#guard decide (parsePathComponent "." = some .current)
#guard decide (parsePathComponent ".." = some .parent)
#guard decide (parsePathComponent ("".pushn 'a' NAME_MAX) ≠ none)        -- exactly 255 bytes: OK
#guard decide (parsePathComponent ("".pushn 'a' (NAME_MAX + 1)) = none)  -- 256 bytes: rejected

-- --- Raw parsing (no PATH_MAX check yet) -------------------------------

#guard decide (parsePosixPathRaw "/var/log/syslog" =
  some (.absolute [nc! "var", nc! "log", nc! "syslog"]))
#guard decide (parsePosixPathRaw "config.json" = some (.relative [nc! "config.json"]))
#guard decide (parsePosixPathRaw "./scripts/deploy.sh" =
  some (.relative [.current, nc! "scripts", nc! "deploy.sh"]))
#guard decide (parsePosixPathRaw "../logs/error.log" =
  some (.relative [.parent, nc! "logs", nc! "error.log"]))
#guard decide (parsePosixPathRaw ".." = some (.relative [.parent]))
#guard decide (parsePosixPathRaw "../" = some (.relative [.parent]))
#guard decide (parsePosixPathRaw ".../" = some (.relative [nc! "..."]))
#guard decide (parsePosixPathRaw "." = some (.relative [.current]))
#guard decide (parsePosixPathRaw "./" = some (.relative [.current]))
#guard decide (parsePosixPathRaw "" = none)

-- A component that's individually too long fails the *raw* parse too,
-- since `parsePathComponent` already enforces `NAME_MAX`.
#guard decide (parsePosixPathRaw ("/" ++ "".pushn 'a' 300) = none)

-- --- Fully validated parsing: PATH_MAX -------------------------------

#guard decide ((parsePosixPath "/var/log/syslog").map (·.path) =
  some (.absolute [nc! "var", nc! "log", nc! "syslog"]))
#guard decide ((parsePosixPath "/var/log/syslog").map (·.path.toString) =
  some "/var/log/syslog")

-- 18 segments of 250 bytes + 17 separators = 4517 bytes > PATH_MAX (4095),
-- even though every individual segment is well under NAME_MAX (255).
def longSeg : String := "".pushn 'a' 250
def tooLongPath : String := "/" ++ String.intercalate "/" (List.replicate 18 longSeg)

#guard decide (parsePosixPathRaw tooLongPath ≠ none)  -- every component is individually fine
#guard decide (parsePosixPath tooLongPath = none)      -- but the whole path is too long

end Posix.Tests
