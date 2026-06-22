module
public import NonEmpty.String
public import TypedPath.PathCommon
public import Lean.Data.Lsp.Utf16
public import TypedPath.Utf16LengthTheorem

@[expose] public section

/-!
# Windows paths

Windows measures lengths in **UTF-16 code units** (`String.utf16Length` from
`PathCommon.lean`), not bytes — most characters cost `1` unit, astral-plane
characters (emoji etc., needing a surrogate pair) cost `2`.

Two limits matter:

* `SEGMENT_MAX` — a single path component must be non-empty and at most
  `255` UTF-16 code units.
* The whole-path limit depends on the prefix:
  * `LEGACY_PATH_MAX = 259` — the usable text under the classic
    `MAX_PATH = 260` limit (`260` minus the `NUL` terminator), which applies
    to ordinary drive/UNC/relative paths.
  * `VERBATIM_PATH_MAX = 32767` — for paths using the `\\?\` (or
    `\\?\UNC\`) verbatim prefix, which bypasses the legacy limit.

We deliberately do **not** model the `LongPathsEnabled` registry/group-policy
setting: whether that's on is a property of the machine and the running
process's manifest, not of the path string, so a parser can't determine it
just by looking at the text. If you need to support that, the right place to
plumb it through is as an extra `Bool` argument to `WindowsPrefix.maxLen`.
-/

open NonEmpty.String

namespace Windows

/-- Maximum length of a single path component, in UTF-16 code units. -/
def SEGMENT_MAX : Nat := 255

/-- Maximum length of a Windows UNC server name, in UTF-16 code units. -/
def SERVER_MAX : Nat := 255

/-- Maximum length of a Windows SMB share name, in UTF-16 code units. -/
def SHARE_MAX : Nat := 80

/-- Usable text length under the legacy `MAX_PATH = 260` limit (i.e.
    `260` minus the `NUL` terminator), in UTF-16 code units. -/
def LEGACY_PATH_MAX : Nat := 259

/-- Usable text length for verbatim (`\\?\` / `\\?\UNC\`) paths, in UTF-16
    code units. -/
def VERBATIM_PATH_MAX : Nat := 32767

def isWinSep (c : Char) : Bool := c == '\\' || c == '/'

def isDriveLetter (c : Char) : Bool :=
  (c >= 'A' && c <= 'Z') || (c >= 'a' && c <= 'z')

/-- A drive letter, always canonicalised to upper-case `'A'..'Z'`. -/
structure ValidDriveChar where
  toChar : Char
  is_upper_az : 'A' ≤ toChar ∧ toChar ≤ 'Z' := by decide
deriving DecidableEq

/-- Smart constructor: upper-cases `c`, then checks it lands in `'A'..'Z'`. -/
def ValidDriveChar.mk? (c : Char) : Option ValidDriveChar :=
  let u := c.toUpper
  if h : 'A' ≤ u ∧ u ≤ 'Z' then some ⟨u, h⟩ else none

instance : Inhabited ValidDriveChar := ⟨{ toChar := 'A' }⟩

def ValidDriveChar.mk! (c : Char) : ValidDriveChar :=
  match ValidDriveChar.mk? c with
  | some v => v
  | none => panic! s!"Invalid drive char: {c}"

macro "utf16Length_decide" : tactic => `(tactic| (simp only [String.utf16Length_eq, Char.utf16Size_eq]; decide))

/-- A path-component name that is non-empty and at most `SEGMENT_MAX`
    *UTF-16 code units* long. -/
structure ValidComponent extends NonEmptyString where
  len_le : toString.utf16Length ≤ SEGMENT_MAX := by utf16Length_decide
deriving DecidableEq

instance : ToString ValidComponent := ⟨(·.toString)⟩

def ValidComponent.mk? (s : String) : Option ValidComponent :=
  if h1 : s ≠ "" then
    if h2 : s.utf16Length ≤ SEGMENT_MAX then
      some { toString := s, isNonEmpty := h1, len_le := h2 }
    else none
  else none

instance : Inhabited ValidComponent := ⟨{ toString := "Inhabited ValidComponent" }⟩

def ValidComponent.mk! (s : String) : ValidComponent :=
  match ValidComponent.mk? s with
  | some v => v
  | none => panic! s!"Invalid component: {s}"

theorem ValidComponent.utf16Length_le (c : ValidComponent) :
    c.toString.utf16Length ≤ SEGMENT_MAX := c.len_le

/-- A validated Windows UNC server name.
    Must be non-empty and at most `255` UTF-16 code units long. -/
structure ValidServer extends NonEmptyString where
  len_le : toString.utf16Length ≤ SERVER_MAX := by utf16Length_decide
deriving DecidableEq

instance : ToString ValidServer := ⟨(·.toString)⟩

def ValidServer.mk? (s : String) : Option ValidServer :=
  if h1 : s ≠ "" then
    if h2 : s.utf16Length ≤ SERVER_MAX then
      some { toString := s, isNonEmpty := h1, len_le := h2 }
    else none
  else none

instance : Inhabited ValidServer := ⟨{ toString := "Inhabited ValidServer" }⟩

def ValidServer.mk! (s : String) : ValidServer :=
  match ValidServer.mk? s with
  | some v => v
  | none => panic! s!"Invalid server: {s}"

theorem ValidServer.utf16Length_le (s : ValidServer) :
    s.toString.utf16Length ≤ SERVER_MAX := s.len_le

/-- A validated Windows SMB share name.
    Must be non-empty and at most `80` UTF-16 code units long. -/
structure ValidShare extends NonEmptyString where
  len_le : toString.utf16Length ≤ SHARE_MAX := by utf16Length_decide
deriving DecidableEq

instance : ToString ValidShare := ⟨(·.toString)⟩

def ValidShare.mk? (s : String) : Option ValidShare :=
  if h1 : s ≠ "" then
    if h2 : s.utf16Length ≤ SHARE_MAX then
      some { toString := s, isNonEmpty := h1, len_le := h2 }
    else none
  else none

instance : Inhabited ValidShare := ⟨{ toString := "Inhabited ValidShare" }⟩

def ValidShare.mk! (s : String) : ValidShare :=
  match ValidShare.mk? s with
  | some v => v
  | none => panic! s!"Invalid share: {s}"

theorem ValidShare.utf16Length_le (s : ValidShare) :
    s.toString.utf16Length ≤ SHARE_MAX := s.len_le

inductive PathComponent where
  | current
  | parent
  | normal (name : ValidComponent)
deriving DecidableEq

def PathComponent.toString : PathComponent → String
  | .current  => "."
  | .parent   => ".."
  | .normal n => n.toString

instance : ToString PathComponent := ⟨PathComponent.toString⟩

def parsePathComponent (s : String) : Option PathComponent :=
  if s == "." then some .current
  else if s == ".." then some .parent
  else (ValidComponent.mk? s).map .normal

inductive WindowsPrefix where
  | driveAbsolute (drive : ValidDriveChar)                  -- "C:\"
  | driveRelative (drive : ValidDriveChar)                  -- "D:" (relative to current drive dir)
  | currentDriveAbsolute                                    -- "\" (absolute from current drive root)
  | unc (server : ValidServer) (share : ValidShare)         -- r"\Server\Share"
  | verbatimDisk (drive : ValidDriveChar)                   -- r"\?\C:\"
  | verbatimUnc (server : ValidServer) (share : ValidShare) -- r"\?\UNC\Server\Share"
  | relative                                                -- no prefix
deriving DecidableEq

structure WindowsPath where
  prefix_ : WindowsPrefix
  components : List PathComponent
deriving DecidableEq

def WindowsPrefix.toString : WindowsPrefix → String
  | .driveAbsolute d          => String.singleton d.toChar ++ ":\\"
  | .driveRelative d          => String.singleton d.toChar ++ ":"
  | .currentDriveAbsolute     => "\\"
  | .unc server share         => "\\\\" ++ server.toString ++ "\\" ++ share.toString ++ "\\"
  | .verbatimDisk d           => "\\\\?\\" ++ String.singleton d.toChar ++ ":\\"
  | .verbatimUnc server share => "\\\\?\\UNC\\" ++ server.toString ++ "\\" ++ share.toString ++ "\\"
  | .relative                 => ""

def WindowsPrefix.isVerbatim : WindowsPrefix → Bool
  | .verbatimDisk _  => true
  | .verbatimUnc ..  => true
  | _                => false

/-- Maximum allowed length (UTF-16 code units) of the whole serialised path,
    for a given prefix. -/
def WindowsPrefix.maxLen (p : WindowsPrefix) : Nat :=
  if p.isVerbatim then VERBATIM_PATH_MAX else LEGACY_PATH_MAX

def WindowsPath.toString (p : WindowsPath) : String :=
  p.prefix_.toString ++ String.intercalate "\\" (p.components.map PathComponent.toString)

instance : ToString WindowsPath := ⟨WindowsPath.toString⟩

/-- A `WindowsPath` together with a proof that re-serialising it never
    exceeds the length limit appropriate to its prefix (`LEGACY_PATH_MAX`
    for ordinary paths, `VERBATIM_PATH_MAX` for `\\?\`-prefixed ones). -/
structure ValidPath where
  path : WindowsPath
  size_le : path.toString.utf16Length ≤ path.prefix_.maxLen
deriving DecidableEq

instance : ToString ValidPath := ⟨fun vp => vp.path.toString⟩

def WindowsPath.toValid? (p : WindowsPath) : Option ValidPath :=
  if h : p.toString.utf16Length ≤ p.prefix_.maxLen then some ⟨p, h⟩ else none

theorem ValidPath.toString_le_maxLen (vp : ValidPath) :
    vp.path.toString.utf16Length ≤ vp.path.prefix_.maxLen := vp.size_le

-- ---------------------------------------------------------------------
-- Parsing
-- ---------------------------------------------------------------------

def runToSep (cs : List Char) : String × List Char :=
  let rec loop (acc : List Char) : List Char → String × List Char
    | [] => (String.ofList acc.reverse, [])
    | c :: rest =>
      if isWinSep c then
        (String.ofList acc.reverse, rest)
      else
        loop (c :: acc) rest
  loop [] cs

def matchVerbatimUnc : List Char → Option (String × String × List Char)
  | s1 :: s2 :: '?' :: s3 :: 'U' :: 'N' :: 'C' :: s4 :: rest =>
    if isWinSep s1 && isWinSep s2 && isWinSep s3 && isWinSep s4 then
      let (server, rest1) := runToSep rest
      let (share, rest2) := runToSep rest1
      some (server, share, rest2)
    else none
  | _ => none

def matchVerbatimDisk : List Char → Option (ValidDriveChar × List Char)
  | s1 :: s2 :: '?' :: s3 :: d :: ':' :: rest =>
    if isWinSep s1 && isWinSep s2 && isWinSep s3 && isDriveLetter d then
      (ValidDriveChar.mk? d).map (fun vd => (vd, rest))
    else none
  | _ => none

def matchUnc : List Char → Option (String × String × List Char)
  | s1 :: s2 :: rest =>
    if isWinSep s1 && isWinSep s2 then
      let (server, rest1) := runToSep rest
      let (share, rest2) := runToSep rest1
      some (server, share, rest2)
    else none
  | _ => none

def matchDriveAbsolute : List Char → Option (ValidDriveChar × List Char)
  | d :: ':' :: s :: rest =>
    if isDriveLetter d && isWinSep s then
      (ValidDriveChar.mk? d).map (fun vd => (vd, rest))
    else none
  | _ => none

def matchDriveRelative : List Char → Option (ValidDriveChar × List Char)
  | d :: ':' :: rest =>
    if isDriveLetter d then (ValidDriveChar.mk? d).map (fun vd => (vd, rest)) else none
  | _ => none

def matchCurrentDriveAbsolute : List Char → Option (List Char)
  | s :: rest => if isWinSep s then some rest else none
  | _ => none

def parseWinPrefix (cs : List Char) : Option (WindowsPrefix × List Char) :=
  match matchVerbatimUnc cs with
  | some (server, share, rest) =>
    match ValidServer.mk? server, ValidShare.mk? share with
    | some vs, some vsh => some (.verbatimUnc vs vsh, rest)
    | _, _ => none
  | none =>
    match matchVerbatimDisk cs with
    | some (d, rest) => some (.verbatimDisk d, rest)
    | none =>
      match matchUnc cs with
      | some (server, share, rest) =>
        match ValidServer.mk? server, ValidShare.mk? share with
        | some vs, some vsh => some (.unc vs vsh, rest)
        | _, _ => none
      | none =>
        match matchDriveAbsolute cs with
        | some (d, rest) => some (.driveAbsolute d, rest)
        | none =>
          match matchDriveRelative cs with
          | some (d, rest) => some (.driveRelative d, rest)
          | none =>
            match matchCurrentDriveAbsolute cs with
            | some rest => some (.currentDriveAbsolute, rest)
            | none => some (.relative, cs)

/-- Splits and parses every component, failing if any component violates
    `SEGMENT_MAX`. -/
def splitWinComponents (cs : List Char) : Option (List PathComponent) :=
  (splitOnPred cs isWinSep).mapM parsePathComponent

/-- Parses the prefix and components; checks `SEGMENT_MAX` per component,
    but not yet the whole-path limit — see `parseWindowsPath` for that. -/
def parseWindowsPathRaw (s : String) : Option WindowsPath :=
  if s.isEmpty then none
  else
    let cs := s.toList
    match parseWinPrefix cs with
    | some (prefix_, rest) =>
      (splitWinComponents rest).map (fun comps => ⟨prefix_, comps⟩)
    | none => none

/-- Parse a string into a fully-validated Windows path: every component must
    satisfy `SEGMENT_MAX`, and the whole re-serialised path must satisfy the
    limit appropriate to its prefix. -/
def parseWindowsPath (s : String) : Option ValidPath :=
  (parseWindowsPathRaw s).bind WindowsPath.toValid?
