module
public import NonEmpty.String
public import NonEmpty.ListCorrectByConstruction
public import TypedPath.PathCommon
import Aesop

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
`Posix.PosixNormalComponent` or a `Posix.ValidPath` that violates them, because the
only way to build one is through a smart constructor that checks the bound
and hands back the resulting `Nat`-inequality as a proof obligation. Since
every bound here is a concrete, decidable `Nat ≤`, that check is literally
just `Nat.decLe` doing the work — no hand-written proofs (and no `sorry`s)
were actually needed.
-/
open NonEmpty.String
open NonEmpty.ListCorrectByConstruction

namespace Posix

/-- `NAME_MAX`: maximum length of a single path component, in bytes. -/
def POSIX_NORMAL_COMPONENT_MAX : Nat := 255

/-- `PATH_MAX`: maximum length of a whole path, in bytes of text. This is
    `4096 - 1`: the kernel's buffer size minus the terminating `NUL` byte
    that isn't part of the text itself. -/
def POSIX_WHOLE_PATH_MAX : Nat := 4095

/-- A path-component name that is non-empty and at most `NAME_MAX` bytes
    long. -/
structure PosixNormalComponent extends NonEmptyString where
  len_le : toString.utf8ByteSize ≤ POSIX_NORMAL_COMPONENT_MAX := by decide
  not_current : toString ≠ "." := by decide
  not_parent : toString ≠ ".." := by decide
  no_slash : toString.contains '/' = false :=
    by simp_all only [↓Char.isValue, String.contains_char_eq, String.reduceToList, List.mem_cons, Char.reduceEq, List.not_mem_nil, or_self, decide_false]
deriving DecidableEq

instance : ToString PosixNormalComponent := ⟨(·.toString)⟩

namespace PosixNormalComponent

/-- Smart constructor: validates non-emptiness and the `NAME_MAX` bound. -/
def mk? (s : String) : Option PosixNormalComponent :=
  if h : s ≠ "" ∧ s.utf8ByteSize ≤ POSIX_NORMAL_COMPONENT_MAX ∧ s ≠ "." ∧ s ≠ ".." ∧ s.contains '/' = false then
    some {
      toString := s
      isNonEmpty := h.1
      len_le := h.2.1
      not_current := h.2.2.1
      not_parent := h.2.2.2.1
      no_slash := h.2.2.2.2
    }
  else none

instance : Inhabited PosixNormalComponent := ⟨{ toString := "Inhabited PosixNormalComponent" }⟩

def mk! (s : String) : PosixNormalComponent :=
  match mk? s with
  | some v => v
  | none => panic! s!"Invalid component: {s}"

theorem utf8ByteSize_le (c : PosixNormalComponent) : c.toString.utf8ByteSize ≤ POSIX_NORMAL_COMPONENT_MAX := c.len_le

end PosixNormalComponent

/-- A single component of a POSIX path. -/
inductive PosixComponent : Bool → Type where
  | parent : PosixComponent true             -- ".."
  | normal (name : PosixNormalComponent) : PosixComponent allowParents -- a validated file/directory name
deriving DecidableEq

def PosixComponent.toNonEmptyString : PosixComponent allowParents → NonEmptyString
  | .parent   => ⟨"..", by decide⟩
  | .normal n => n.toNonEmptyString

instance : ToString (PosixComponent allowParents) := ⟨(·.toNonEmptyString.toString)⟩

/-- Parses a single path component. `.` and `..` are recognised specially
    (they're not subject to `NAME_MAX` — the kernel treats them as fixed
    pseudo-entries, not arbitrary names); anything else must satisfy
    `PosixNormalComponent`, otherwise the whole parse fails. -/
def parsePathComponent : (allowParents : Bool) → String → Option (PosixComponent allowParents)
  | true, ".." => some .parent
  | _, s => (PosixNormalComponent.mk? s).map .normal

def PosixPath.components_toNonEmptyString (pathType : PathType) (fileType : FileType) (components : NonEmptyList (PosixComponent allowParents)) : NonEmptyString :=
  let base := intercalateListCBC "/" (components.map PosixComponent.toNonEmptyString)
  let prefix_: String := match pathType with
    | .Abs => "/"
    | .Rel => ""
  let suffix_: String := match fileType with
    | .Dir => "/"
    | .File => ""
  prefix_ ++ base ++ suffix_

def PosixPath.components_toString (pathType : PathType) (fileType : FileType) (components : NonEmptyList (PosixComponent allowParents)) : String :=
  PosixPath.components_toNonEmptyString pathType fileType components |> NonEmptyString.toString

/-- A POSIX path, before the whole-path `PATH_MAX` check. -/
-- Absolute means IF true THEN means starts with / ELSE ./foo or foo will be parsed same but printed only to foo
structure PosixPath (allowParents : Bool) (pathType : PathType) (fileType : FileType) where
  components : NonEmptyList (PosixComponent allowParents)
  size_le : (PosixPath.components_toString pathType fileType components).utf8ByteSize ≤ POSIX_WHOLE_PATH_MAX
deriving DecidableEq

instance : ToString (PosixPath allowParents pathType fileType) :=
  ⟨fun p => PosixPath.components_toString pathType fileType p.components⟩

structure ExpectedPosixPath where
  allowParents : Bool
  pathType : PathType
  fileType : FileType
deriving BEq, Inhabited, DecidableEq

inductive IfParentsNotAllowedButHaveParent where
  | Throw
  | Skip
deriving BEq, Inhabited, DecidableEq, Repr

inductive IfRequestedRelButStartsWithSlash where
  | Throw
  | DropSlash
deriving BEq, Inhabited, DecidableEq, Repr

inductive IfRequestedAbsButNoSlash where
  | Throw
  | StillMakeAbs
deriving BEq, Inhabited, DecidableEq, Repr

inductive IfRequestedDirButNoTrailingSlash where
  | Throw
  | StillMakeDir
deriving BEq, Inhabited, DecidableEq, Repr

inductive IfRequestedFileButTrailingSlash where
  | Throw
  | DropTrailingSlash
deriving BEq, Inhabited, DecidableEq, Repr

structure Config where
  ifParentsNotAllowed_whatToDoIfParentIsInInput : IfParentsNotAllowedButHaveParent
  ifRequestedRelButStartsWithSlash : IfRequestedRelButStartsWithSlash
  ifRequestedAbsButNoSlash : IfRequestedAbsButNoSlash
  ifRequestedDirButNoTrailingSlash : IfRequestedDirButNoTrailingSlash
  ifRequestedFileButTrailingSlash : IfRequestedFileButTrailingSlash
deriving BEq, Inhabited

inductive ParseError where
  | ParentWasNotAllowedByPresentInInput
  | RequestedRelButStartsWithSlash
  | RequestedAbsButNoSlash
  | RequestedDirButNoTrailingSlash
  | RequestedFileButTrailingSlash
  | EmptyPath
  | InvalidComponent (name : String)
  | PathTooLong
deriving BEq, DecidableEq, Repr

inductive ParseAutoError where
  | EmptyPath
  | InvalidComponent (name : String)
  | PathTooLong
deriving BEq, DecidableEq, Repr

def parsePathComponentWithConfig (config : IfParentsNotAllowedButHaveParent) : (allowParents : Bool) → String → Except ParseError (Option (PosixComponent allowParents))
  | true, ".." => Except.ok (some .parent)
  | false, ".." =>
    match config with
    | .Throw => Except.error ParseError.ParentWasNotAllowedByPresentInInput
    | .Skip => Except.ok none
  | _, s =>
    match PosixNormalComponent.mk? s with
    | some vc => Except.ok (some (.normal vc))
    | none => Except.error (ParseError.InvalidComponent s)

def splitPosixPath (s : String) (hasPrefixSlash : Bool) : List String :=
  let rest := if hasPrefixSlash then s.toList.drop 1 else s.toList
  splitOnPred rest (· == '/') |>.filter (· ≠ ".")

/-- Parses every component of a `/`-separated path, failing the whole parse
    if *any* component violates `NAME_MAX`. Also checks that the whole
    re-serialised path satisfies `PATH_MAX`. -/
def parsePosixPath (expected : ExpectedPosixPath) (config : Config) (s : String) : Except ParseError (PosixPath expected.allowParents expected.pathType expected.fileType) := do
  let hasPrefixSlash := s.startsWith "/"
  let hasSuffixSlash := s.endsWith "/"

  if expected.pathType == .Rel ∧ hasPrefixSlash then
    if config.ifRequestedRelButStartsWithSlash == .Throw then
      throw ParseError.RequestedRelButStartsWithSlash
  if expected.pathType == .Abs ∧ ¬hasPrefixSlash then
    if config.ifRequestedAbsButNoSlash == .Throw then
      throw ParseError.RequestedAbsButNoSlash

  if expected.fileType == .Dir ∧ ¬hasSuffixSlash then
    if config.ifRequestedDirButNoTrailingSlash == .Throw then
      throw ParseError.RequestedDirButNoTrailingSlash
  if expected.fileType == .File ∧ hasSuffixSlash then
    if config.ifRequestedFileButTrailingSlash == .Throw then
      throw ParseError.RequestedFileButTrailingSlash

  let parts := splitPosixPath s hasPrefixSlash
  let comps ← parts.filterMapM (parsePathComponentWithConfig config.ifParentsNotAllowed_whatToDoIfParentIsInInput expected.allowParents)

  match NonEmptyList.fromList? comps with
  | none => throw ParseError.EmptyPath
  | some neParts =>
    if h : (PosixPath.components_toString expected.pathType expected.fileType neParts).utf8ByteSize ≤ POSIX_WHOLE_PATH_MAX then
      Except.ok ⟨neParts, h⟩
    else
      throw ParseError.PathTooLong

structure AnyPosixPath where
  allowParents : Bool
  pathType : PathType
  fileType : FileType
  path : PosixPath allowParents pathType fileType

def parsePathComponentAuto : (allowParents : Bool) → String → Except ParseAutoError (Option (PosixComponent allowParents))
  | true, ".." => Except.ok (some .parent)
  | false, ".." => Except.ok none -- should never be reached in Auto
  | _, s =>
    match PosixNormalComponent.mk? s with
    | some vc => Except.ok (some (.normal vc))
    | none => Except.error (ParseAutoError.InvalidComponent s)

def parsePosixPathAuto (s : String) : Except ParseAutoError AnyPosixPath := do
  let hasPrefixSlash := s.startsWith "/"
  let pathType := if hasPrefixSlash then PathType.Abs else PathType.Rel
  let fileType := if s.endsWith "/" then FileType.Dir else FileType.File
  let parts := splitPosixPath s hasPrefixSlash
  let allowParents := ".." ∈ parts

  let comps ← parts.filterMapM (parsePathComponentAuto allowParents)

  match NonEmptyList.fromList? comps with
  | none => throw ParseAutoError.EmptyPath
  | some neParts =>
    if h : (PosixPath.components_toString pathType fileType neParts).utf8ByteSize ≤ POSIX_WHOLE_PATH_MAX then
      Except.ok ⟨allowParents, pathType, fileType, ⟨neParts, h⟩⟩
    else
      throw ParseAutoError.PathTooLong
