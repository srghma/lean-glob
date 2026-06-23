module
import Lean
public import Lean.Elab.Term.TermElabM
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
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

instance : ToString PosixNormalComponent := ⟨(·.toString)⟩

instance : LT PosixNormalComponent where
  lt a b := a.toNonEmptyString < b.toNonEmptyString

instance : LE PosixNormalComponent where
  le a b := a.toNonEmptyString ≤ b.toNonEmptyString

instance (a b : PosixNormalComponent) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.toNonEmptyString < b.toNonEmptyString))

instance (a b : PosixNormalComponent) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.toNonEmptyString ≤ b.toNonEmptyString))

instance : Min PosixNormalComponent where
  min a b := if a ≤ b then a else b

instance : Max PosixNormalComponent where
  max a b := if a ≤ b then b else a

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
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

def PosixComponent.toNonEmptyString : PosixComponent allowParents → NonEmptyString
  | .parent   => ⟨"..", by decide⟩
  | .normal n => n.toNonEmptyString

instance : ToString (PosixComponent allowParents) := ⟨(·.toNonEmptyString.toString)⟩

instance {ap} : LT (PosixComponent ap) where
  lt a b := compare a b == .lt

instance {ap} : LE (PosixComponent ap) where
  le a b := compare a b != .gt

instance {ap} (a b : PosixComponent ap) : Decidable (a < b) :=
  inferInstanceAs (Decidable (compare a b == .lt))

instance {ap} (a b : PosixComponent ap) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (compare a b != .gt))

instance {ap} : Min (PosixComponent ap) where
  min a b := if a ≤ b then a else b

instance {ap} : Max (PosixComponent ap) where
  max a b := if a ≤ b then b else a

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
inductive PosixPath (allowParents : Bool) (pathType : PathType) (fileType : FileType) : Bool → Type where
  | cwd : PosixPath allowParents pathType fileType true
  | path {allowCwd : Bool}
    (components : NonEmptyList (PosixComponent allowParents))
    (size_le : (PosixPath.components_toString pathType fileType components).utf8ByteSize ≤ POSIX_WHOLE_PATH_MAX)
    : PosixPath allowParents pathType fileType allowCwd
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

instance : ToString (PosixPath allowParents pathType fileType allowCwd) :=
  ⟨fun
    | .cwd => "."
    | .path components _ => PosixPath.components_toString pathType fileType components⟩

structure ExpectedPosixPath where
  allowCwd : Bool
  allowParents : Bool
  pathType : PathType
  fileType : FileType
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive IfCwdNotAllowedButInputIsCwd where
  | Throw
  | Skip
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive IfParentsNotAllowedButHaveParent where
  | Throw
  | Skip
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive IfRequestedRelButStartsWithSlash where
  | Throw
  | DropSlash
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive IfRequestedAbsButNoSlash where
  | Throw
  | StillMakeAbs
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive IfRequestedDirButNoTrailingSlash where
  | Throw
  | StillMakeDir
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive IfRequestedFileButTrailingSlash where
  | Throw
  | DropTrailingSlash
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

structure Config where
  allowTrailingSeparator : Bool
  treatTwoOrMoreRepeatingSeparatorsAsOne : Bool
  cwdIsNotAllowedButInputIsCwd : IfCwdNotAllowedButInputIsCwd
  ifParentsNotAllowed_whatToDoIfParentIsInInput : IfParentsNotAllowedButHaveParent
  ifRequestedRelButStartsWithSlash : IfRequestedRelButStartsWithSlash
  ifRequestedAbsButNoSlash : IfRequestedAbsButNoSlash
  ifRequestedDirButNoTrailingSlash : IfRequestedDirButNoTrailingSlash
  ifRequestedFileButTrailingSlash : IfRequestedFileButTrailingSlash
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

inductive ParseAutoError where
  | EmptyPath
  | InvalidComponent (name : String)
  | PathTooLong
deriving BEq, Hashable, Ord, Repr, DecidableEq, ReflBEq, LawfulBEq

instance : ToString ParseAutoError where
  toString
  | .EmptyPath => "The parsed path contains no valid components (e.g. empty string or only skipped components)."
  | .InvalidComponent name => s!"Invalid path component: `{name}`. Components cannot exceed POSIX_NORMAL_COMPONENT_MAX ({POSIX_NORMAL_COMPONENT_MAX}) bytes and cannot contain `/`."
  | .PathTooLong => s!"The fully resolved path exceeds the POSIX_WHOLE_PATH_MAX ({POSIX_WHOLE_PATH_MAX}) limit."

inductive ParseError where
  | RepeatingSeparatorsNotAllowed
  | TrailingSeparatorNotAllowed
  | CwdNotAllowedButInputIsCwd
  | ParentWasNotAllowedByPresentInInput
  | RequestedRelButStartsWithSlash
  | RequestedAbsButNoSlash
  | RequestedDirButNoTrailingSlash
  | RequestedFileButTrailingSlash
  | EmptyPath
  | InvalidComponent (name : String)
  | PathTooLong
deriving BEq, DecidableEq, Repr

instance : ToString ParseError where
  toString
  | .RepeatingSeparatorsNotAllowed => "Repeating separators (e.g. `foo//bar` or `foo///bar`) are not allowed by the configuration."
  | .TrailingSeparatorNotAllowed => "Trailing separators (e.g. `foo/`) are not allowed by the configuration."
  | .CwdNotAllowedButInputIsCwd => "The current working directory (e.g. `.` or `./`) is not allowed by the configuration."
  | .ParentWasNotAllowedByPresentInInput => "Parent directory components (`..`) are not allowed by the configuration."
  | .RequestedRelButStartsWithSlash => "A relative path was requested, but the input starts with a slash (`/`)."
  | .RequestedAbsButNoSlash => "An absolute path was requested, but the input does not start with a slash (`/`)."
  | .RequestedDirButNoTrailingSlash => "A directory path was requested, but the input does not end with a trailing slash (`/`)."
  | .RequestedFileButTrailingSlash => "A file path was requested, but the input ends with a trailing slash (`/`)."
  | .EmptyPath => "The parsed path contains no valid components (e.g. empty string or only skipped components)."
  | .InvalidComponent name => s!"Invalid path component: `{name}`. Components cannot exceed POSIX_NORMAL_COMPONENT_MAX ({POSIX_NORMAL_COMPONENT_MAX}) bytes and cannot contain `/`."
  | .PathTooLong => s!"The fully resolved path exceeds the POSIX_WHOLE_PATH_MAX ({POSIX_WHOLE_PATH_MAX}) limit."

def ParseAutoError.toParseError : ParseAutoError → ParseError
  | .EmptyPath => .EmptyPath
  | .InvalidComponent s => .InvalidComponent s
  | .PathTooLong => .PathTooLong

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
  splitOnPred rest (· == '/') |>.filter (fun c => c ≠ "." ∧ c ≠ "")

def containsTwoSlashes (s : String) : Bool :=
  let rec go : List Char → Bool
    | '/' :: '/' :: _ => true
    | _ :: t => go t
    | [] => false
  go s.toList

def PosixPath.mk? {allowCwd allowParents pathType fileType} (comps : List (PosixComponent allowParents)) : Except ParseAutoError (PosixPath allowParents pathType fileType allowCwd) :=
  match NonEmptyList.fromList? comps with
  | none => Except.error ParseAutoError.EmptyPath
  | some neParts =>
    if h : (PosixPath.components_toString pathType fileType neParts).utf8ByteSize ≤ POSIX_WHOLE_PATH_MAX then
      Except.ok (.path neParts h)
    else
      Except.error ParseAutoError.PathTooLong

/-- Append one validated component to an existing path, changing its `FileType`
    to `newFt`. Returns `none` only if the resulting path would exceed PATH_MAX. -/
def PosixPath.appendNormalComponent? {allowParents pathType fileType allowCwd}
    (p : PosixPath allowParents pathType fileType allowCwd)
    (c : PosixNormalComponent)
    (newFt : FileType) : Option (PosixPath allowParents pathType newFt false) :=
  let newComps : NonEmptyList (PosixComponent allowParents) :=
    match p with
    | .cwd    => { head := PosixComponent.normal (allowParents := allowParents) c, tail := [] }
    | .path cs _ => { head := cs.head, tail := cs.tail ++ [PosixComponent.normal c] }
  if h : (PosixPath.components_toString pathType newFt newComps).utf8ByteSize ≤ POSIX_WHOLE_PATH_MAX then
    some (.path newComps h)
  else
    none


/-- Parses every component of a `/`-separated path, failing the whole parse
    if *any* component violates `NAME_MAX`. Also checks that the whole
    re-serialised path satisfies `PATH_MAX`. -/
def parsePosixPath (expected : ExpectedPosixPath) (config : Config) (s : String) : Except ParseError (PosixPath expected.allowParents expected.pathType expected.fileType expected.allowCwd) := do
  let hasPrefixSlash := s.startsWith "/"
  let hasSuffixSlash := s.endsWith "/"

  if ¬config.treatTwoOrMoreRepeatingSeparatorsAsOne ∧ containsTwoSlashes s then
    throw ParseError.RepeatingSeparatorsNotAllowed

  if ¬config.allowTrailingSeparator ∧ s.length > 1 ∧ hasSuffixSlash then
    throw ParseError.TrailingSeparatorNotAllowed

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

  if s == "." ∨ s == "./" then
    if h : expected.allowCwd then
      return h ▸ .cwd
    else
      if config.cwdIsNotAllowedButInputIsCwd == .Throw then
        throw ParseError.CwdNotAllowedButInputIsCwd

  let parts := splitPosixPath s hasPrefixSlash
  let comps ← parts.filterMapM (parsePathComponentWithConfig config.ifParentsNotAllowed_whatToDoIfParentIsInInput expected.allowParents)

  match PosixPath.mk? comps with
  | Except.ok p => Except.ok p
  | Except.error e => Except.error e.toParseError

structure AnyPosixPath where
  allowCwd : Bool
  allowParents : Bool
  pathType : PathType
  fileType : FileType
  path : PosixPath allowParents pathType fileType allowCwd

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

  if s == "." ∨ s == "./" then
    return ⟨true, false, pathType, fileType, .cwd⟩

  let parts := splitPosixPath s hasPrefixSlash
  let allowParents := ".." ∈ parts

  let comps ← parts.filterMapM (parsePathComponentAuto allowParents)

  match PosixPath.mk? comps with
  | Except.ok p => Except.ok ⟨false, allowParents, pathType, fileType, p⟩
  | Except.error e => Except.error e

open Lean Elab Term Meta

syntax posixPathNamedArg := "(" ident ":=" term ")"
syntax "posixPath! " posixPathNamedArg* str : term

elab_rules : term
| `(posixPath! $[( $ids:ident := $terms:term )]* $s:str) => do
  let mut apStx? : Option Term := none
  let mut acStx? : Option Term := none
  for id in ids, t in terms do
    if id.getId == `allowParents then apStx? := some t
    else if id.getId == `allowCwd then acStx? := some t
    else throwErrorAt id "unknown argument, expected 'allowParents' or 'allowCwd'"

  let str := s.getString
  let hasPrefixSlash := str.startsWith "/"
  let pathTypeStx : Term ← if hasPrefixSlash then `(PathType.Abs) else `(PathType.Rel)
  let fileTypeStx : Term ← if str.endsWith "/" then `(FileType.Dir) else `(FileType.File)

  if str == "." ∨ str == "./" then
    let acStx ← match acStx? with | some t => pure t | none => `(true)
    let apStx ← match apStx? with | some t => pure t | none => `(false)
    let stx ← `( (PosixPath.cwd : PosixPath $apStx $pathTypeStx $fileTypeStx $acStx) )
    elabTerm stx none
  else
    let parts := str.splitOn "/" |>.filter (fun c => c ≠ "." ∧ c ≠ "")
    let allowParents := parts.contains ".."
    let allowParentsStx ← match apStx? with
      | some t => pure t
      | none => if allowParents then `(true) else `(false)
    let allowCwdStx ← match acStx? with | some t => pure t | none => `(false)

    if parts.isEmpty then
      throwError "posixPath! error: Empty path"

    let mut totalSize := parts.foldl (fun acc p => acc + p.utf8ByteSize) 0
    totalSize := totalSize + parts.length - 1
    if hasPrefixSlash then totalSize := totalSize + 1
    if str.endsWith "/" then totalSize := totalSize + 1
    if totalSize > 4096 then
      throwError "posixPath! error: Path too long"

    let quoteComp (c : String) : MacroM Term := do
      if c == ".." then
        `(PosixComponent.parent)
      else
        if c.utf8ByteSize > 255 then
          Macro.throwError s!"posixPath! error: Component {c} too long"
        let sStx := quote c
        `(PosixComponent.normal ({ toNonEmptyString := { toString := $sStx, isNonEmpty := by decide } } : PosixNormalComponent))

    let hdStx ← liftMacroM (quoteComp parts.head!)
    let rec quoteList : List String → MacroM Term
      | [] => `([])
      | x :: xs => do
        let xStx ← quoteComp x
        let xsStx ← quoteList xs
        `( $xStx :: $xsStx )

    let tlStx ← liftMacroM (quoteList parts.tail!)
    let compsStx ← `( ⟨$hdStx, $tlStx⟩ )

    let stx ← `( (PosixPath.path $compsStx (by decide) : PosixPath $allowParentsStx $pathTypeStx $fileTypeStx $allowCwdStx) )
    elabTerm stx none
