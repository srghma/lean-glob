module
public import NonEmpty.String
public import TypedPath.PathCommon

@[expose] public section

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
