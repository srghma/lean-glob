module
public import Init.System.FilePath
public import Init.Data.Option.Basic
public import Init.Data.String.Basic
public import NonEmpty.String

@[expose] public section

namespace Pathy

open NonEmpty.String (NonEmptyString)

/-!
# Pathy

A `FilePath` wrapper indexed by `PathType` (`Rel` / `Abs`) and `FileType`
(`Dir` / `File`), backed by a **list of segments** rather than a raw,
re-validated string.

Why segments instead of a validated `String`:

* "no doubled separator", "canonical separator", "no leading `.`" all become
  *unrepresentable* instead of *checked*: we only ever insert exactly one
  separator, ourselves, between two segments, at render time.
* `extendPath` / `appendPath` become literal `List.append`. The one
  remaining proof obligation (`segments = [] → pathKind = .Abs ∧ ft = .Dir`)
  discharges by `List` lemmas, no string induction required.
* Parsing an *external* `FilePath`/`String` into this form is still
  genuinely partial (arbitrary external input can be malformed), so that
  direction keeps `?`/`!` pairs. The internal combinators do not need them.

One real, structural limitation (not a shortcut): a relative path with
exactly one segment has no representable parent, because going up would
land on the banned `.`. `parentOf?` / `peel?` are therefore `Option`, and
that is inherent to disallowing `.`, not a missing proof.
-/

/-- Phantom-ish tag: is this path meant to be relative or absolute. -/
inductive PathType where
  | Rel
  | Abs
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- Phantom-ish tag: does this path denote a directory or a file. -/
inductive FileType where
  | Dir
  | File
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The OS path separator character(s) we treat as "a separator". Mirrors
`System.FilePath.pathSeparators`, duplicated here so this file has no
dependency on the exact private name in `Init.System.FilePath`. -/
def pathSeparators : List Char :=
  if System.Platform.isWindows then ['\\', '/'] else ['/']

/-- The single canonical separator we ever *emit*. -/
def canonicalSep : Char :=
  if System.Platform.isWindows then '\\' else '/'

/-- A single path segment: a non-empty string containing no separator
character, and not equal to `.` or `..` (those are navigation, not names). -/
structure Name extends NonEmptyString where
  noSep : ∀ c ∈ toString.toList, ¬ pathSeparators.contains c := by decide
  notDot : toString ≠ "." := by decide
  notDotDot : toString ≠ ".." := by decide
  deriving DecidableEq, Hashable, Repr

instance : ToString Name where
  toString n := n.toNonEmptyString.toString

instance : Inhabited Name where
  default :=
    { toString := "DEFAULT Name"
      isNonEmpty := by decide
      noSep := by grind? }

/-- Build a `Name`, checking all three side conditions. `Decidable` all the
way down, so this is a plain `if h : _ then _ else none`, no manual proof. -/
def Name.fromString? (s : String) : Option Name :=
  if h1 : s ≠ "" then
    if h2 : ∀ c ∈ s.toList, ¬ pathSeparators.contains c then
      if h3 : s ≠ "." then
        if h4 : s ≠ ".." then
          some { toString := s
                 isNonEmpty := h1, noSep := h2, notDot := h3, notDotDot := h4 }
        else none
      else none
    else none
  else none

def Name.fromString! (s : String) : Name :=
  match Name.fromString? s with
  | some n => n
  | none   => panic! s!"Pathy.Name.fromString!: invalid path segment {s}"

/-- The data underlying every `Pathy` path: a `PathType` tag and a list of
segments, with the invariant that an *empty* segment list can only mean
"the absolute root directory" — never a relative path, and never a file
(a file always has a name, i.e. a last segment). -/
structure AnyPath (ft : FileType) where
  pathKind : PathType
  segments : List Name
  rootInvariant : segments = [] → pathKind = .Abs ∧ ft = .Dir
  deriving Hashable, Repr

abbrev AnyDir := AnyPath .Dir
abbrev AnyFile := AnyPath .File

instance : DecidableEq (AnyPath ft) :=
  fun p q =>
    if h1 : p.pathKind = q.pathKind then
      if h2 : p.segments = q.segments then
        isTrue (by cases p; cases q; subst h1; subst h2; rfl)
      else
        isFalse (fun h => h2 (by rw [h]))
    else
      isFalse (fun h => h1 (by rw [h]))

/-- `Path pt ft`: an `AnyPath ft` whose `pathKind` is pinned to `pt`.
Same data as `AnyPath`, with the `PathType` promoted from a field to an
index — this is the type users mostly write down. -/
def Path (pt : PathType) (ft : FileType) := { p : AnyPath ft // p.pathKind = pt }

abbrev RelPath (ft : FileType) := Path .Rel ft
abbrev AbsPath (ft : FileType) := Path .Abs ft
abbrev RelDir  := Path .Rel .Dir
abbrev AbsDir  := Path .Abs .Dir
abbrev RelFile := Path .Rel .File
abbrev AbsFile := Path .Abs .File

instance : DecidableEq (Path pt ft) := Subtype.instDecidableEqSubtype
instance : Hashable (Path pt ft) where
  hash p := hash p.val
instance : Repr (Path pt ft) where
  reprPrec p n := reprPrec p.val n

/-- Lift `AnyPath` data with a known `pathKind` into the indexed `Path`. -/
@[inline] def AnyPath.toPath (p : AnyPath ft) (h : p.pathKind = pt := by rfl) : Path pt ft :=
  ⟨p, h⟩

@[inline] def Path.toAnyPath (p : Path pt ft) : AnyPath ft := p.val

instance : Coe (Path pt ft) (AnyPath ft) := ⟨Path.toAnyPath⟩

/-! ## Rendering to `System.FilePath` -/

def AnyPath.toFilePath (p : AnyPath ft) : System.FilePath :=
  let body := canonicalSep.toString.intercalate (p.segments.map toString)
  match p.pathKind with
  | .Abs => ⟨canonicalSep.toString ++ body⟩
  | .Rel => ⟨body⟩  -- segments is provably non-empty here, see rootInvariant

def Path.toFilePath (p : Path pt ft) : System.FilePath := p.toAnyPath.toFilePath

instance : ToString (AnyPath ft) where
  toString p := p.toFilePath.toString

instance : ToString (Path pt ft) where
  toString p := p.toFilePath.toString

/-! ## Basic constructors -/

/-- The root directory `/`. -/
def rootDir : AbsDir :=
  ⟨{ pathKind := .Abs, segments := [], rootInvariant := fun _ => ⟨rfl, rfl⟩ }, rfl⟩

/-- A bare relative file/dir consisting of a single segment. -/
def single (pt : PathType) (n : Name) : AnyPath ft :=
  { pathKind := pt
    segments := [n]
    rootInvariant := fun h => absurd h (by simp) }

def file (n : Name) : RelFile := (single .Rel n : AnyPath .File).toPath
def dir  (n : Name) : RelDir  := (single .Rel n : AnyPath .Dir).toPath

/-! ## extendPath / appendPath — total, no `?` / `!` -/

/-- Extend a directory with one more named segment, landing in either a
file or a directory depending on `ft`. Total: appending a non-empty list
([n]) can never produce `[]`. -/
def extendPath (base : AnyPath .Dir) (n : Name) : AnyPath ft :=
  { pathKind := base.pathKind
    segments := base.segments ++ [n]
    rootInvariant := fun h => absurd h (by simp) }

instance : HDiv (AnyPath .Dir) Name (AnyPath ft) where
  hDiv := extendPath

/-- `</>` is just notation for the `HDiv` instance above, kept for
readability / familiarity with `System.FilePath`'s `/`. -/
infixl:65 " </> " => extendPath

/-- Append a *relative* path onto a directory. Total: `rel.pathKind = .Rel`
forces `rel.segments ≠ []` (contrapositive of `rootInvariant`), so the
concatenation can only be `[]` if both sides are, which is impossible. -/
def appendPath (base : AnyPath .Dir) (rel : AnyPath ft) (h : rel.pathKind = .Rel) :
    AnyPath ft :=
  have relNonempty : rel.segments ≠ [] := by
    intro hEmpty
    have := rel.rootInvariant hEmpty
    rw [h] at this
    exact absurd this.1 (by decide)
  { pathKind := base.pathKind
    segments := base.segments ++ rel.segments
    rootInvariant := fun hEq => absurd (List.append_eq_nil.mp hEq).2 relNonempty }

/-- `<//>` restricted, via the `pathKind` field, to genuinely relative
right-hand sides — pass the `RelPath` directly and the proof comes for
free from its index. -/
def appendRelPath {pt : PathType} (base : Path pt .Dir) (rel : RelPath ft) : Path pt ft :=
  (appendPath base.toAnyPath rel.toAnyPath rel.property).toPath
    (by simp [appendPath, base.property])

infixl:65 " <//> " => appendRelPath

/-! ## Parent navigation -/

/-- The parent directory, dropping the last segment. `none` only for the
absolute root (no parent) or a single-segment relative path (the parent
would be `.`, which is banned, so it is not representable). -/
def AnyPath.parentOf? (p : AnyPath ft) : Option (AnyPath .Dir) :=
  match p.segments with
  | [] => none                      -- root: no parent
  | [_] =>
      if h : p.pathKind = .Abs then
        some { pathKind := .Abs, segments := [], rootInvariant := fun _ => ⟨rfl, rfl⟩ }
      else
        none                        -- relative single segment: parent is `.`, banned
  | _ :: _ :: _ =>
      some { pathKind := p.pathKind
             segments := p.segments.dropLast
             rootInvariant := fun hEq => by
               exfalso
               have hlen := congrArg List.length hEq
               simp [List.length_dropLast] at hlen }

def Path.parentOf? (p : Path pt ft) : Option (Path pt .Dir) :=
  p.toAnyPath.parentOf?.map (·.toPath (by
    rcases p with ⟨ap, hk⟩
    rcases ap with ⟨pathKind, segments, _⟩
    subst hk
    cases segments with
    | nil => rfl
    | cons _ tl => cases tl <;> simp_all [AnyPath.parentOf?]))

/-- Go up one level then descend into a relative path — total composition
of two already-total operations, modulo the inherent partiality of
`parentOf?` itself. -/
def parentAppend? {pt : PathType} (base : Path pt .Dir) (rel : RelPath ft) :
    Option (Path pt ft) :=
  base.parentOf?.map (· <//> rel)

/-- `/../`, notation for `parentAppend?`. -/
infixl:65 " /../ " => parentAppend?

/-! ## Peeling: split a path into its parent and final `Name` -/

structure PathComponents (pt : PathType) (ft : FileType) where
  parent : Path pt .Dir
  name : Name
  deriving Repr

def AnyPath.peel? (p : AnyPath ft) : Option (PathComponents p.pathKind ft) := do
  match h : p.segments with
  | [] => none
  | _ :: _ =>
      let parent ← p.parentOf?
      have hk : parent.pathKind = p.pathKind := by
        rcases p with ⟨pathKind, segments, inv⟩
        simp only at h
        cases segments with
        | nil => cases h
        | cons hd tl =>
            cases tl with
            | nil =>
                simp [AnyPath.parentOf?] at *
                split at parent <;> simp_all
            | cons _ _ => simp [AnyPath.parentOf?] at *
      some ⟨parent.toPath hk, p.segments.getLast (by simp [h])⟩

/-- For files we can guarantee `peel?` succeeds: a `File` always has at
least one segment (the file's own name) by `rootInvariant`. -/
def AbsFile.peel (p : Path pt .File) : PathComponents pt .File :=
  match h : p.toAnyPath.peel? with
  | some pc => h ▸ pc
  | none =>
      absurd (p.toAnyPath.rootInvariant (by
        by_contra hne
        rw [AnyPath.peel?] at h
        cases p.toAnyPath.segments <;> simp_all)).2
        (by decide)

/-- The terminal segment's name, for any path that has one. -/
def AnyPath.name? (p : AnyPath ft) : Option Name := p.segments.getLast?

def Path.name? (p : Path pt ft) : Option Name := p.toAnyPath.name?

/-- Files always have a name. -/
def AbsFile.name (p : Path pt .File) : Name :=
  match p.name? with
  | some n => n
  | none => panic! "Pathy: a File-tagged path with no segments — invariant violated"

/-! ## Renaming / extensions -/

def rename (f : Name → Name) (p : Path pt ft) : Path pt ft :=
  match h : p.toAnyPath.peel? with
  | some pc => pc.parent </> f pc.name
  | none => p  -- root has no name to rename; identity

/-- Change the extension of the final segment, when there is one. -/
def setExtension (p : Path pt ft) (ext : String) : Path pt ft :=
  rename (fun n =>
    let s := toString n
    let stem := (System.FilePath.mk s).withExtension ext |>.toString
    Name.fromString! stem) p

infixl:65 " <.> " => setExtension

/-! ## AnyPath as a "this could be either" union, without an inductive -/

/-- `AnyPathType ft` is the type of paths of file-kind `ft` whose
relative/absolute status is *not* known statically. This is exactly the
`AnyPath ft` structure above (we don't need a separate `rel | abs`
inductive — the `pathKind` field already records which one it is, and
`Path pt ft` is recovered from it by pinning the index). -/
abbrev AnyPathType (ft : FileType) := AnyPath ft

/-- Recover a `RelPath` if the dynamic tag says `.Rel`. -/
def AnyPath.asRel? (p : AnyPath ft) : Option (RelPath ft) :=
  if h : p.pathKind = .Rel then some (p.toPath h) else none

/-- Recover an `AbsPath` if the dynamic tag says `.Abs`. -/
def AnyPath.asAbs? (p : AnyPath ft) : Option (AbsPath ft) :=
  if h : p.pathKind = .Abs then some (p.toPath h) else none

/-! ## Parsing external `FilePath` / `String` — genuinely partial -/

/-- Split a raw string on separator characters, drop empty pieces from
leading/duplicate separators, and reject any segment that is `.` or `..`
(callers wanting `..`-navigation should use `parentAppend?`, not parse it
out of a string). -/
def AnyPath.fromFilePath? (fp : System.FilePath) : Option (Σ ft, AnyPath ft) := do
  let raw := fp.toString
  if raw.isEmpty then
    none
  else
    let isAbs := pathSeparators.contains raw.front
    let pieces := (raw.split (pathSeparators.contains ·)).filter (· ≠ "")
    let names ← pieces.mapM Name.fromString?
    let ft : FileType := if pathSeparators.contains raw.back then .Dir else .File
    if names = [] then
      if isAbs then
        some ⟨.Dir, { pathKind := .Abs, segments := [], rootInvariant := fun _ => ⟨rfl, rfl⟩ }⟩
      else
        none  -- "" or "." alone: nothing left to represent
    else
      some ⟨ft, { pathKind := if isAbs then .Abs else .Rel
                  segments := names
                  rootInvariant := fun h => absurd h (by simp_all) }⟩

def AnyPath.fromFilePath! (fp : System.FilePath) : Σ ft, AnyPath ft :=
  match AnyPath.fromFilePath? fp with
  | some r => r
  | none => panic! s!"Pathy: cannot parse path {fp}"

def fromString? (s : String) : Option (Σ ft, AnyPath ft) :=
  AnyPath.fromFilePath? ⟨s⟩

def fromString! (s : String) : Σ ft, AnyPath ft :=
  AnyPath.fromFilePath! ⟨s⟩

/-- Parse expecting a specific shape; `none` if the dynamic tags don't
match what was asked for. -/
def parseAs? (pt : PathType) (ft : FileType) (s : String) : Option (Path pt ft) := do
  let ⟨ft', p⟩ ← fromString? s
  if h : ft' = ft then
    (h ▸ p).asRelOrAbs pt
  else
    none
where
  AnyPath.asRelOrAbs (p : AnyPath ft) (pt : PathType) : Option (Path pt ft) :=
    if h : p.pathKind = pt then some (p.toPath h) else none

def parseAs! (pt : PathType) (ft : FileType) (s : String) : Path pt ft :=
  match parseAs? pt ft s with
  | some p => p
  | none => panic! s!"Pathy: {s} is not a valid {repr pt} {repr ft} path"

def parseAbsFile (s : String) : Option AbsFile := parseAs? .Abs .File s
def parseAbsDir  (s : String) : Option AbsDir  := parseAs? .Abs .Dir s
def parseRelFile (s : String) : Option RelFile := parseAs? .Rel .File s
def parseRelDir  (s : String) : Option RelDir  := parseAs? .Rel .Dir s

/-! ## Helpers -/

def isAbsolute (p : AnyPath ft) : Bool := p.pathKind matches .Abs
def isRelative (p : AnyPath ft) : Bool := p.pathKind matches .Rel

end Pathy

/-! ## `Pathy.IO` — the `System.FilePath`-typed primitives, retyped -/

namespace Pathy.IO

open _root_.IO (FileRight)
open _root_.IO.FS (DirEntry FileType Metadata Handle Mode)
open _root_.System (FilePath)
open Pathy (AnyFile AnyDir AnyPath AbsFile AbsDir Path PathType Pathy.FileType)

/-- Wrap a `FilePath` the OS handed back, into the path type we *claim* to
be returning. `panic!`s if our assumption about the OS's contract turns
out to be wrong at runtime — this is the one place raw OS strings re-enter
the typed world, so it is also the one place a contract violation can
still surface (as a panic, not silently). -/
def wrapAbs! (ft : Pathy.FileType) (fp : FilePath) : AbsFile :=
  match Pathy.AnyPath.fromFilePath? fp with
  | some ⟨ft', p⟩ =>
      if h1 : ft' = ft then
        if h2 : p.pathKind = .Abs then
          (h1 ▸ p).toPath h2
        else
          panic! s!"Pathy.IO: expected an absolute path, OS returned {fp}"
      else
        panic! s!"Pathy.IO: expected a {repr ft} path, OS returned {fp}"
  | none => panic! s!"Pathy.IO: OS returned unparseable path {fp}"

def wrapAbsFile! (fp : FilePath) : AbsFile := wrapAbs! .File fp
def wrapAbsDir!  (fp : FilePath) : AbsDir  := wrapAbs! .Dir fp

-- Handle-based operations: take an `AnyFile` (caller's path could be
-- relative or absolute — `IO.FS.Handle.mk` itself imposes no such
-- restriction), unwrap to the underlying `FilePath` at the FFI boundary.

def Handle.mk (fn : AnyFile) (mode : Mode) : _root_.IO Handle :=
  _root_.IO.FS.Handle.mk fn.toFilePath mode

def realPath (fname : AnyPath ft) : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.FS.realPath fname.toFilePath

def removeFile (fname : AnyFile) : _root_.IO Unit :=
  _root_.IO.FS.removeFile fname.toFilePath

def removeDir (p : AnyDir) : _root_.IO Unit :=
  _root_.IO.FS.removeDir p.toFilePath

def createDir (p : AnyDir) : _root_.IO Unit :=
  _root_.IO.FS.createDir p.toFilePath

def rename (old new : AnyPath ft) : _root_.IO Unit :=
  _root_.IO.FS.rename old.toFilePath new.toFilePath

def createTempFile : _root_.IO (Handle × AbsFile) := do
  let (h, fp) ← _root_.IO.FS.createTempFile
  return (h, wrapAbsFile! fp)

def createTempDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.FS.createTempDir

def appPath : _root_.IO AbsFile :=
  wrapAbsFile! <$> _root_.IO.appPath

def currentDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.currentDir

def withFile (fn : AnyFile) (mode : Mode) (f : Handle → _root_.IO α) : _root_.IO α :=
  _root_.IO.FS.withFile fn.toFilePath mode f

def lines (fname : AnyFile) : _root_.IO (Array String) :=
  _root_.IO.FS.lines fname.toFilePath

def writeBinFile (fname : AnyFile) (content : ByteArray) : _root_.IO Unit :=
  _root_.IO.FS.writeBinFile fname.toFilePath content

def writeFile (fname : AnyFile) (content : String) : _root_.IO Unit :=
  _root_.IO.FS.writeFile fname.toFilePath content

def DirEntry.path (entry : DirEntry) : AbsFile :=
  -- `IO.FS.DirEntry.path` is documented to always be absolute.
  wrapAbsFile! (_root_.IO.FS.DirEntry.path entry)

def readDir (p : AnyDir) : _root_.IO (Array DirEntry) :=
  _root_.System.FilePath.readDir p.toFilePath

def metadata (p : AnyPath ft) : _root_.IO Metadata :=
  _root_.System.FilePath.metadata p.toFilePath

def isDir (p : AnyPath ft) : BaseIO Bool :=
  _root_.System.FilePath.isDir p.toFilePath

def pathExists (p : AnyPath ft) : BaseIO Bool :=
  _root_.System.FilePath.pathExists p.toFilePath

/-- `walkDir` is the one exception left returning raw `FilePath`s: a
single walk legitimately mixes files and directories, and there is no
single `ft` to retype the result against. -/
def walkDir (p : AnyDir) (enter : FilePath → _root_.IO Bool := fun _ => pure true) :
    _root_.IO (Array FilePath) :=
  _root_.System.FilePath.walkDir p.toFilePath enter

def readBinFile (fname : AnyFile) : _root_.IO ByteArray :=
  _root_.IO.FS.readBinFile fname.toFilePath

def readFile (fname : AnyFile) : _root_.IO String :=
  _root_.IO.FS.readFile fname.toFilePath

def appDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.appDir

def createDirAll (p : AnyDir) : _root_.IO Unit :=
  _root_.IO.FS.createDirAll p.toFilePath

def removeDirAll (p : AnyDir) : _root_.IO Unit :=
  _root_.IO.FS.removeDirAll p.toFilePath

def withTempFile [Monad m] [MonadFinally m] [MonadLiftT _root_.IO m]
    (f : Handle → AbsFile → m α) : m α :=
  _root_.IO.FS.withTempFile (fun h fp => f h (wrapAbsFile! fp))

def withTempDir [Monad m] [MonadFinally m] [MonadLiftT _root_.IO m]
    (f : AbsDir → m α) : m α :=
  _root_.IO.FS.withTempDir (fun fp => f (wrapAbsDir! fp))

def getCurrentDir : _root_.IO AbsDir :=
  wrapAbsDir! <$> _root_.IO.Process.getCurrentDir

def setCurrentDir (path : AnyDir) : _root_.IO Unit :=
  _root_.IO.Process.setCurrentDir path.toFilePath

def setAccessRightsPrim (filename : AnyPath ft) (mode : UInt32) : _root_.IO Unit :=
  _root_.IO.Prim.setAccessRights filename.toFilePath mode

def setAccessRights (filename : AnyPath ft) (mode : FileRight) : _root_.IO Unit :=
  _root_.IO.setAccessRights filename.toFilePath mode

end Pathy.IO
