/-
  System.Path — a Lean 4 port of Idris2's `contrib` library
  https://github.com/idris-lang/Idris2/blob/main/libs/contrib/System/Path.idr

  This is a from-scratch reimplementation, not a mechanical transliteration:

  * Idris' `</>` (String → String → String) is replaced by an `HDiv String
    String String` instance, so plain `/` works: `"a" / "b" : String`.
    Idris' `/>` (Path → String → Path) is replaced by `HDiv Path String Path`
    and `HDiv Path Path Path`.
  * Idris parses with `Text.Lexer` / `Text.Parser`. The path grammar here is
    regular, so a hand-written scanner over `List Char` is used instead.
  * Where it was natural I leaned on `String.Slice`-flavoured helpers
    (`String.splitOn`, `List.span`, `Char` predicates) to avoid building
    throwaway `String`s while scanning, materialising a `String` only once
    per final path component (mirrors `Init/System/FilePath.lean`'s use of
    slicing for `fileName`/`extension`/`parent`).
  * Two small bugs in the original were *not* ported:
      - Idris' `Eq Volume` compares `r1 == r2` instead of `l2 == r2` for the
        UNC case (looks like a typo). Fixed here.
      - Idris' post-parse cleanup uses `delete CurDir xs`, which (per
        `Data.List.delete`) removes only the *first* `"."` from the tail of
        the body list. The doc comment on `parse` describes removing *all*
        embedded `"."`s, which is what this port actually does.

-/

namespace System.Path

/-- Whether we are targeting Windows, used to decide separator conventions. -/
def isWindows : Bool := Platform.isWindows

/-- The preferred directory separator on this platform. -/
def sep : Char := if isWindows then '\\' else '/'

/-- Both `/` and `\` count as separators when *parsing*, regardless of
platform — matching the original Idris parser, which always accepts either
slash style and leaves platform-specific interpretation (e.g. `isAbsolute`)
to a later pass. -/
def isPathSep (c : Char) : Bool := c == '/' || c == '\\'

--------------------------------------------------------------------------------
-- Types
--------------------------------------------------------------------------------

/-- Windows path prefix. -/
inductive Volume where
  /-- Windows Uniform Naming Convention: server name and share directory.
  Example: `\\localhost\share` -/
  | unc (server share : String) -- TODO: add prof that both are valid. (only ascii, right? what is max lenght?)
  /-- A drive letter. Example: `C:` -/
  | disk (drive : Char) -- TODO: add proof that char is uppercase
  deriving BEq, DecidableEq, Repr, Inhabited

/-- A single body element in a path. -/
inductive Body where
  /-- `"."` -/
  | curDir
  /-- `".."` -/
  | parentDir
  /-- A regular directory or file name. -/
  | normal (s : String)
  deriving BEq, DecidableEq, Repr, Inhabited

/--
A parsed, cross-platform file system path.

Use `System.Path.parse` to build one from a `String`, and `toString` /
`ToString` to go back. Trailing separators only affect display, and are
ignored by equality (see the `BEq Path` instance below).
-/
structure Path where
  /-- Windows path prefix (only meaningful on Windows). -/
  volume : Option Volume := none
  /-- Whether the path contains a root. -/
  hasRoot : Bool := false
  /-- The path bodies. -/
  body : List Body := []
  /-- Whether the path terminates with a separator. -/
  hasTrailSep : Bool := false
  deriving Repr, Inhabited

instance : BEq Path where
  beq a b := a.volume == b.volume && a.hasRoot == b.hasRoot && a.body == b.body

--------------------------------------------------------------------------------
-- Show
--------------------------------------------------------------------------------

def Body.toStr : Body → String
  | .curDir => "."
  | .parentDir => ".."
  | .normal s => s

instance : ToString Body := ⟨Body.toStr⟩

def Volume.toStr : Volume → String
  | .unc server share => "\\\\" ++ server ++ "\\" ++ share
  | .disk drive => String.singleton drive ++ ":"

instance : ToString Volume := ⟨Volume.toStr⟩

/-- Displays the path in the format of this platform. -/
def Path.toStr (p : Path) : String :=
  let s := String.singleton sep
  let showVol := p.volume.map Volume.toStr |>.getD ""
  let showRoot := if p.hasRoot then s else ""
  let showBody := s.intercalate (p.body.map Body.toStr)
  let showTrail := if p.hasTrailSep then s else ""
  showVol ++ showRoot ++ showBody ++ showTrail

instance : ToString Path := ⟨Path.toStr⟩

--------------------------------------------------------------------------------
-- Parser
--------------------------------------------------------------------------------

/-- Read characters up to (not including) the next separator, `:` or `?`. -/
private def readText (cs : List Char) : List Char × List Char :=
  cs.span (fun c => !(c == '/' || c == '\\' || c == ':' || c == '?'))

/-- Try to read a `\\server\share` body (the two leading backslashes must
already have been stripped by the caller). -/
private def tryUncBody (cs : List Char) : Option (Volume × List Char) :=
  let (serverChars, rest1) := readText cs
  if serverChars.isEmpty then none else
  match rest1 with
  | c :: rest2 =>
    if isPathSep c then
      let (shareChars, rest3) := readText rest2
      if shareChars.isEmpty then none
      else some (.unc (String.ofList serverChars) (String.ofList shareChars), rest3)
    else none
  | [] => none

/-- Try to read a `C:` drive prefix. Mirrors the Idris parser: only the
*first* character of the text before `:` is used as the drive letter. -/
private def tryDisk (cs : List Char) : Option (Volume × List Char) :=
  let (textChars, rest1) := readText cs
  match textChars, rest1 with
  | d :: _, ':' :: rest2 => some (.disk d.toUpper, rest2)
  | _, _ => none

/-- Parses an optional volume prefix: verbatim (`\\?\...`) UNC or disk,
plain UNC, or plain disk. Returns the remaining characters either way. -/
private def tryParseVolume (cs : List Char) : Option Volume × List Char :=
  match cs with
  | '\\' :: '\\' :: '?' :: '\\' :: rest =>
    -- verbatim prefix: try UNC, then disk; on failure treat the whole
    -- prefix as ordinary (unparsed) text, like the rest of the parser does
    -- with anything it can't make sense of.
    match tryUncBody rest with
    | some (v, rest') => (some v, rest')
    | none =>
      match tryDisk rest with
      | some (v, rest') => (some v, rest')
      | none => (none, cs)
  | '\\' :: '\\' :: rest =>
    match tryUncBody rest with
    | some (v, rest') => (some v, rest')
    | none =>
      match tryDisk cs with
      | some (v, rest') => (some v, rest')
      | none => (none, cs)
  | _ =>
    match tryDisk cs with
    | some (v, rest') => (some v, rest')
    | none => (none, cs)

/-- Strip a leading run of separators. Returns whether any were stripped. -/
private def stripLeadingSeps (cs : List Char) : Bool × List Char :=
  let (taken, rest) := cs.span isPathSep
  (!taken.isEmpty, rest)

/-- Strip a trailing run of separators. Returns whether any were stripped. -/
private def stripTrailingSeps (cs : List Char) : Bool × List Char :=
  let (taken, rest) := cs.reverse.span isPathSep
  (!taken.isEmpty, rest.reverse)

/-- Split a list of characters into maximal runs of non-separator
characters, the way `sepBy (some bodySeparator) parseBody` does in the
original — consecutive separators produce empty groups in between, which
the caller filters out. -/
private def splitChars (cs : List Char) : List (List Char) :=
  match cs with
  | [] => [[]]
  | c :: rest =>
    let groups := splitChars rest
    if isPathSep c then
      [] :: groups
    else
      match groups with
      | g :: gs => (c :: g) :: gs
      | [] => [[c]] -- unreachable: splitChars never returns []

private def isBlank (s : String) : Bool := s.trimAscii.isEmpty

private def classifyBody (s : String) : Body :=
  if s == ".." then .parentDir
  else if s == "." then .curDir
  else .normal s

/--
Parses a `String` into a `Path`.

The relax rules (same as the Idris original):

- Both `/` and `\` are parsed as valid directory separators, regardless of
  platform;
- any characters are allowed in a body, e.g. `/root/*`;
- a verbatim prefix (`\\?\`, Windows-only) is recognised and consumed;
- repeated separators are collapsed, so `"a/b"` and `"a//b"` both have `"a"`
  and `"b"` as bodies;
- `"."` in the body is removed unless it's at the very beginning of the
  path: `"a/./b"`, `"a/b/"`, `"a/b/."` and `"a/b"` all have `"a"`, `"b"` as
  bodies, while `"./a/b"` starts with `Body.curDir`.

```
parse "C:\\Windows/System32"
parse "/usr/local/etc/*"
```
-/
def parse (str : String) : Path :=
  let cs0 := str.toList
  let (volOpt, cs1) := tryParseVolume cs0
  let (hasRoot, cs2) := stripLeadingSeps cs1
  let (hasTrail, cs3) := stripTrailingSeps cs2
  let strs := (splitChars cs3).map String.ofList |>.filter (fun s => !isBlank s)
  let bodies := strs.map classifyBody
  let bodies := match bodies with
    | [] => []
    | b :: bs => b :: bs.filter (· != .curDir)
  { volume := volOpt, hasRoot, body := bodies, hasTrailSep := hasTrail }

--------------------------------------------------------------------------------
-- Path-level utilities
--------------------------------------------------------------------------------

/--
Whether the path is absolute.

- On Unix, a path is absolute iff it has a root, so `isAbsolute` and
  `hasRoot` agree.
- On Windows, a path is absolute iff it has a disk *and* a root, or it's a
  UNC path. E.g. `C:\windows` is absolute, while `C:temp` and `\temp` are
  not.
-/
def Path.isAbsolute (p : Path) : Bool :=
  if isWindows then
    match p.volume with
    | some (.unc ..) => true
    | some (.disk _) => p.hasRoot
    | none => false
  else
    p.hasRoot

def Path.isRelative (p : Path) : Bool := !p.isAbsolute

/--
Appends `right` to `left`.

If `right` is absolute, it replaces `left` entirely. On Windows: if `right`
has a root but no volume, it replaces everything but `left`'s volume; if it
has a volume but no root, it replaces `left` outright.
-/
def Path.append (left right : Path) : Path :=
  if right.isAbsolute || right.volume.isSome then
    right
  else if right.hasRoot then
    { right with volume := left.volume }
  else
    { left with body := left.body ++ right.body, hasTrailSep := right.hasTrailSep }

instance : HDiv Path Path Path := ⟨Path.append⟩
instance : HDiv Path String Path := ⟨fun l r => l.append (parse r)⟩
instance : HDiv String String String := ⟨fun l r => toString ((parse l).append (parse r))⟩

private def splitBodyGroups : List Body → Bool → List Path
  | [], _ => []
  | [x], trail => [{ body := [x], hasTrailSep := trail }]
  | x :: y :: xs, trail => ({ body := [x] } : Path) :: splitBodyGroups (y :: xs) trail

/-- Splits a path into its single-element components, longest-prefix
(volume/root) first if present. Trailing separator is preserved only on
the discarded equality, but `toString` of the last component reflects it. -/
def Path.split (p : Path) : List Path :=
  if p.volume.isNone && !p.hasRoot then
    splitBodyGroups p.body p.hasTrailSep
  else
    let root : Path := { volume := p.volume, hasRoot := p.hasRoot }
    root :: splitBodyGroups p.body p.hasTrailSep

/-- Splits the path into a parent `Path` and a final-component `Path`. -/
def Path.splitParent (p : Path) : Option (Path × Path) :=
  match p.body.reverse with
  | [] => none
  | last :: revInit =>
    let parent : Path := { p with body := revInit.reverse, hasTrailSep := false }
    let child : Path := { body := [last], hasTrailSep := p.hasTrailSep }
    some (parent, child)

/-- The path without its final component, if there is one. `none` if the
path terminates at a root or volume. -/
def Path.parent (p : Path) : Option Path := p.splitParent.map Prod.fst

private partial def iterateParents (p : Path) : List Path :=
  p :: match p.parent with
    | some pp => iterateParents pp
    | none => []

/-- All parents of the path, longest first, including the path itself. -/
def Path.parents (p : Path) : List Path := iterateParents p

/-- The last body of the path: the file/dir name if the last body is
`Body.normal`; recurses past a trailing `Body.curDir`; `none` for
`Body.parentDir` or an empty body list. -/
def Path.fileName (p : Path) : Option String :=
  go p.body.reverse
where
  go : List Body → Option String
    | [] => none
    | .normal s :: _ => some s
    | .curDir :: rest => go rest
    | .parentDir :: _ => none

/-- Splits a file name into `(stem, extension)` at the last `.`. No `.`, or
a name that's only `.`s, yields `(name, "")`. -/
def splitFileName (name : String) : String × String :=
  match name.toList.reverse.span (· != '.') with
  | (_, []) => (name, "")
  | (_, ['.']) => (name, "")
  | (revExt, _ :: revStem) => (String.ofList revStem.reverse, String.ofList revExt.reverse)

/--
Splits a file name into a basename and a list of extensions. A leading dot
is considered part of the basename.

```
splitExtensions "Path.lean"           = ("Path", ["lean"])
splitExtensions "file.tar.gz"         = ("file", ["tar", "gz"])
splitExtensions ".hidden.tar.gz"      = (".hidden", ["tar", "gz"])
```
-/
def splitExtensions (name : String) : String × List String :=
  match name.splitOn "." with
  | "" :: base :: exts => ("." ++ base, exts)
  | base :: exts => (base, exts)
  | [] => (name, [])

/-- The file name without its extension, if there's a file name at all. -/
def Path.fileStem (p : Path) : Option String :=
  p.fileName.map (Prod.fst ∘ splitFileName)

/-- The extension of the file name, if there's a file name and it has one. -/
def Path.extension (p : Path) : Option String :=
  p.fileName.bind fun n =>
    let ext := (splitFileName n).snd
    if ext == "" then none else some ext

/-- All extensions of the file name (see `splitExtensions`), if there's a
file name. -/
def Path.extensionsAll (p : Path) : Option (List String) :=
  p.fileName.map (Prod.snd ∘ splitExtensions)

/-- Replaces the file name in the path. If there's no file name yet, the
name is appended; otherwise it replaces the existing one. -/
def Path.setFileName (name : String) (p : Path) : Path :=
  if p.fileName.isSome then
    (p.parent.getD default).append (parse name)
  else
    p.append (parse name)

private def listBodyPrefixOf : List Body → List Body → Bool
  | [], _ => true
  | _ :: _, [] => false
  | x :: xs, y :: ys => x == y && listBodyPrefixOf xs ys

/-- Whether `base` is one of the parents of `target` (trailing separators
are ignored). -/
def Path.isBaseOf (base target : Path) : Bool :=
  base.volume == target.volume
    && base.hasRoot == target.hasRoot
    && listBodyPrefixOf base.body target.body

private def dropBodyPrefix : List Body → List Body → Option (List Body)
  | [], ys => some ys
  | _ :: _, [] => none
  | x :: xs, y :: ys => if x == y then dropBodyPrefix xs ys else none

/-- A path that, when appended to `base`, yields `target`. `none` if `base`
is not a prefix of `target`. -/
def Path.dropBase (base target : Path) : Option Path :=
  if base.volume == target.volume && base.hasRoot == target.hasRoot then
    (dropBodyPrefix base.body target.body).map fun b =>
      ({ body := b, hasTrailSep := target.hasTrailSep } : Path)
  else
    none

--------------------------------------------------------------------------------
-- String-level convenience API (mirrors the Idris public surface)
--------------------------------------------------------------------------------

/-- Whether the path string is absolute. -/
def isAbsolute (s : String) : Bool := (parse s).isAbsolute

/-- Whether the path string is relative. -/
def isRelative (s : String) : Bool := !(isAbsolute s)

/-- Joins path components into one. `joinPath ["/usr", "local/etc"] =
"/usr/local/etc"`. -/
def joinPath (xs : List String) : String :=
  toString (xs.foldl (fun (acc : Path) s => acc.append (parse s)) default)

/-- Splits a path string into components. `splitPath "/usr/local/etc" =
["/", "usr", "local", "etc"]`. -/
def splitPath (s : String) : List String := (parse s).split.map toString

/-- Splits a path string into `(parent, child)`. -/
def splitParent (s : String) : Option (String × String) :=
  (parse s).splitParent.map fun (p, c) => (toString p, toString c)

/-- The path string without its final component, if there is one. -/
def parent (s : String) : Option String := (parse s).parent.map toString

/-- All parents of the path string, longest first, self included.
`parents "/etc/kernel" = ["/etc/kernel", "/etc", "/"]`. -/
def parents (s : String) : List String := (parse s).parents.map toString

/-- Whether `base` is one of the parents of `target`. -/
def isBaseOf (base target : String) : Bool := (parse base).isBaseOf (parse target)

/-- A path that, when appended to `base`, yields `target`. -/
def dropBase (base target : String) : Option String :=
  ((parse base).dropBase (parse target)).map toString

/-- The last body of the path string, if there's a usable file/dir name. -/
def fileName (s : String) : Option String := (parse s).fileName

/-- The file name without its extension, if there's a file name. -/
def fileStem (s : String) : Option String := (parse s).fileStem

/-- The extension of the file name, if there's a file name with one. -/
def extension (s : String) : Option String := (parse s).extension

/-- All extensions of the file name, if there's a file name. -/
def extensions (s : String) : Option (List String) := (parse s).extensionsAll

/-- Updates the file name in the path string. Appends if there isn't one
yet, otherwise replaces it. -/
def setFileName (name path : String) : String :=
  toString ((parse path).setFileName name)

/--
Sets the extension of the path string.

- No file name in the path → unchanged.
- No existing extension → the extension is appended.
- `ext == ""` → the extension is dropped.
- Otherwise → the extension is replaced.

`"/tmp/Foo" <.> "lean" == "/tmp/Foo.lean"`
-/
def setExtension (path ext : String) : String :=
  let cleaned := String.ofList (ext.toList.dropWhile (fun c => c == '.' || c.isWhitespace))
  let ext' := if cleaned.isEmpty then "" else "." ++ cleaned
  match (parse path).fileName with
  | some name =>
    let (stem, _) := splitFileName name
    setFileName (stem ++ ext') path
  | none => path

@[inherit_doc setExtension]
infixl:65 " <.> " => setExtension

/-- Drops the extension of the path string. -/
def dropExtension (path : String) : String := path <.> ""

end System.Path
