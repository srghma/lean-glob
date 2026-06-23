here is lean FilePath file
I want to have a wrapper around FilePath called Pathy
it has two params

```lean4
-- Phantom types for path classification
inductive PathType where
  | Rel -- Relative path
  | Abs -- Absolute path
def CompliesToPathType (f : System.FilePath) : PathType -> Prop
  | Rel -> f.isRelative
  | Abs -> f.isAbsolute
inductive FileType where
  | Dir  -- Directory
  | File -- File
def CompliesToFileType (f : System.FileFile) : FileType -> Prop
  | Dir -> s.endWith "/"
  | File -> not s.endWith "/"
-- The main Path type with phantom type parameters
structure Path (pathType : PathType) (fileType : FileType) where
  toFilePath : System.FilePath
  compliesToPathType :
  compliesToFileType :
  deriving Inhabited, DecidableEq, Hashable, Repr -- Ord
also Path should have proof that it is nonempty string and it has no repeating // or \\ depending on os windows or linux
then continue finishing Pathy.lean
```

instead of

```lean4
infixl:65 " </> " => extendPath
use instance HDiv
infixl:65 " <//> " => appendPath
instead of 
infixl:65 " <..> " => parentAppend
maybe /../
```

if possible to implement

```lean4
-- Union types for paths that can be either absolute or relative
inductive AnyPath (ft : FileType) where
  | rel : RelPath ft → AnyPath ft
  | abs : AbsPath ft → AnyPath ft
without using inductives - lets try
Name should be def NonEmptyString
from my lib import NonEmpty.String
module
@[expose] public section
namespace NonEmpty.String
structure NonEmptyString where
  toString : String
  isNonEmpty : toString ≠ ""
  deriving BEq, Hashable, Ord, Repr, DecidableEq
instance : CoeOut NonEmptyString String where
  coe s := s.toString
instance : ToString NonEmptyString where
  toString s := s.toString
namespace NonEmptyString
abbrev fromString? (s : String) : Option NonEmptyString := if h : s ≠ "" then some ⟨s, h⟩ else none
abbrev fromNELChar (cs : List Char) (h : cs ≠ []) : NonEmptyString :=
  ⟨String.ofList cs, by simp_all only [ne_eq, String.ofList_eq_empty_iff, not_false_eq_true]⟩
abbrev fromLChar? (cs : List Char) : Option NonEmptyString := fromString? (String.ofList cs)
@[simp] theorem toString_ne_empty (s : NonEmptyString) : s.toString ≠ "" := s.isNonEmpty
instance : HAppend String NonEmptyString NonEmptyString where
  hAppend s1 s2 := ⟨s1 ++ s2.toString, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, and_false, not_false_eq_true]⟩
instance : HAppend NonEmptyString String NonEmptyString where
  hAppend s1 s2 := ⟨s1.toString ++ s2, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, false_and, not_false_eq_true]⟩
instance : HAppend NonEmptyString NonEmptyString NonEmptyString where
  hAppend s1 s2 := ⟨s1.toString ++ s2.toString, by simp only [ne_eq, String.append_eq_empty_iff,
    toString_ne_empty, and_self, not_false_eq_true]⟩
end NonEmptyString
macro "nes!" s:str : term => do
  let strVal := s.getString
  if strVal.isEmpty then
    Lean.Macro.throwErrorAt s "String literal cannot be empty for nes!"
  else
    ``( (NonEmptyString.mk $s (by decide) : NonEmptyString) )
#guard (nes!"world").toString == "world"
end NonEmpty.String
```

and lets implement

```lean4
def SafePath.IO.FS.Handle.mk (fn : FilePath) (mode : Mode) : IO Handle := _root_.IO.FS.Handle.mk fn mode
def SafePath.IO.FS.realPath (fname : FilePath) : IO FilePath := _root_.IO.FS.realPath fname
def SafePath.IO.FS.removeFile (fname : FilePath) : IO Unit := _root_.IO.FS.removeFile fname
def SafePath.IO.FS.removeDir (p : FilePath) : IO Unit := _root_.IO.FS.removeDir p
def SafePath.IO.FS.createDir (p : FilePath) : IO Unit := _root_.IO.FS.createDir p
def SafePath.IO.FS.rename (old new : FilePath) : IO Unit := _root_.IO.FS.rename old new
def SafePath.IO.FS.createTempFile : IO (Handle × FilePath) := _root_.IO.FS.createTempFile
def SafePath.IO.FS.createTempDir : IO FilePath := _root_.IO.FS.createTempDir
def SafePath.IO.appPath : IO FilePath := _root_.IO.appPath
def SafePath.IO.currentDir : IO FilePath := _root_.IO.currentDir
def SafePath.IO.FS.withFile (fn : FilePath) (mode : Mode) (f : Handle → IO α) : IO α := _root_.IO.FS.withFile fn mode f
def SafePath.IO.FS.lines (fname : FilePath) : IO (Array String) := _root_.IO.FS.lines fname
def SafePath.IO.FS.writeBinFile (fname : FilePath) (content : ByteArray) : IO Unit := _root_.IO.FS.writeBinFile fname content
def SafePath.IO.FS.writeFile (fname : FilePath) (content : String) : IO Unit := _root_.IO.FS.writeFile fname content
def SafePath.IO.FS.DirEntry.path (entry : DirEntry) : FilePath := _root_.IO.FS.DirEntry.path entry
def SafePath.System.FilePath.readDir (p : FilePath) : IO (Array IO.FS.DirEntry) := _root_.System.FilePath.readDir p
def SafePath.System.FilePath.metadata (p : FilePath) : IO IO.FS.Metadata := _root_.System.FilePath.metadata p
def SafePath.System.FilePath.isDir (p : FilePath) : BaseIO Bool := _root_.System.FilePath.isDir p
def SafePath.System.FilePath.pathExists (p : FilePath) : BaseIO Bool := _root_.System.FilePath.pathExists p
def SafePath.System.FilePath.walkDir (p : FilePath) (enter : FilePath → IO Bool := fun _ => pure true) : IO (Array FilePath) := _root_.System.FilePath.walkDir p enter
def SafePath.IO.FS.readBinFile (fname : FilePath) : IO ByteArray := _root_.IO.FS.readBinFile fname
def SafePath.IO.FS.readFile (fname : FilePath) : IO String := _root_.IO.FS.readFile fname
def SafePath.IO.appDir : IO FilePath := _root_.IO.appDir
def SafePath.IO.FS.createDirAll (p : FilePath) : IO Unit := _root_.IO.FS.createDirAll p
def SafePath.IO.FS.removeDirAll (p : FilePath) : IO Unit := _root_.IO.FS.removeDirAll p
def SafePath.IO.FS.withTempFile [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : Handle → FilePath → m α) : m α := _root_.IO.FS.withTempFile f
def SafePath.IO.FS.withTempDir [Monad m] [MonadFinally m] [MonadLiftT IO m] (f : FilePath → m α) : m α := _root_.IO.FS.withTempDir f
def SafePath.IO.Process.getCurrentDir : IO FilePath := _root_.IO.Process.getCurrentDir
def SafePath.IO.Process.setCurrentDir (path : FilePath) : IO Unit := _root_.IO.Process.setCurrentDir path
def SafePath.IO.Prim.setAccessRights (filename : FilePath) (mode : UInt32) : IO Unit := _root_.IO.Prim.setAccessRights filename mode
def SafePath.IO.setAccessRights (filename : FilePath) (mode : FileRight) : IO Unit := _root_.IO.setAccessRights filename mode
where it tasks FIlePath - replace with correct Pathy (abs or rel or any, dir or file or any)
```

where returns FilePath - validate before returning , if definitely e.g. Pathy Abs File for example - then use panic! to throw if output is unexpected

AnyPath and Pathy should carry inside just a FilePath + proofs (separators were canonicalized, canonical sep doesnt repeat, btw canonical seps there is no . or .. G dots, if Dir then should end with / else not end with / , if Abs then should start with / on linux and on windows start with Capital letter:// (right?) etc

--------

Design choices made along the way:

* `Path pathType fileType` carries four proofs: non-empty, no doubled separator, `CompliesToPathType`, `CompliesToFileType`. All four predicates are `Decidable`, so every constructor is a `parse?`/`parse!` pair built from `if h : ... then ...` rather than hand-proved terms — that's what lets `extendPath`, `appendPath`, `parentAppend` etc. stay total without real proof obligations at each call site.
* `HDiv (Path pt .Dir) (Name ft) (Path pt ft)` replaces `</>`. `<//>` kept as asked. `/../` is custom notation for `parentAppend!`.
* `AnyPath ft` is just `{ f : FilePath // <file-type compliance> }` — no `rel`/`abs` inductive, the path-type proof is simply absent. `asRel?`/`asAbs?` recover a typed path by re-running the `CompliesToPathType` decision at runtime.
* `Name ft` wraps `NonEmptyString` plus a `validSegment` proof (no embedded separator), rather than its own ad-hoc string type.
* IO wrappers under `Pathy.IO` retype every function against `AnyFile`/`AnyDir`/`AnyPath ft`/`AbsFile`/`AbsDir` as appropriate; anywhere the OS hands back a `FilePath` we're claiming more about (e.g. `appPath`, `currentDir`, `createTempDir`), it's funneled through `wrap!`/`wrapAbs!`, which `panic!`s on a surprise. `walkDir` is the one exception left returning raw `FilePath`s, since a single walk legitimately mixes files and directories.
Spots most likely to need a real fix once you compile:

1. `deriving DecidableEq, Repr, Hashable` on `Path` and `Name` — relies on the deriving handlers being fine with `Prop`-typed fields via proof irrelevance; if your Lean version's handler chokes, swap in hand-written instances that project onto `toFilePath`/`toNonEmptyString`.
2. `CompliesToFileType`'s `getLast?.elim` formulation — double check it matches how you want trailing-separator detection to behave on Windows with mixed `/`/`\`.
3. The `NonEmpty.String` import path (`public import NonEmpty.String`) — adjust to match your actual module name if it differs.

-------------

1. `/-- No two path separators occur back to back (rules out`//`,`\\`,`/\`, …`
`    depending on platform). -/`
`def hasDoubleSep (s : String) : Bool := go s.toList`
`where`
`  go : List Char → Bool`
`    | a :: b :: rest => (pathSeparators.contains a && pathSeparators.contains b) || go (b :: rest)`
`    | _ => false`
this seems like wrong
e.g. if using
def pathSeparators : List Char :=   if isWindows then ['\\', '/'] else ['/']
then it will match even if a and b are diff. isnt it?
2.

`| .Dir  => f.toString.toList.getLast?.elim false (pathSeparators.contains ·) = true`
`| .File => f.toString.toList.getLast?.elim false (pathSeparators.contains ·) = false`
there is no need to create intermediate toList
to implement we will actaully :

* the normalizer actually does 2 things
* * in windows it capitalizes drive letter
* * then in windows it canonicalizes separator (replaces pathSeparators [\\ or /] with cannonical \\
lets instead write our own Prop checks and add into Pathy too
then when we will do `def CompliesToFileType (f : FilePath) : FileType → Prop we will also pass proof that separators were already canonicalized`
this way we will just need to check last char on is it cannocial to find our if our path describes path to dir
much easier

1. we have parse? and parse! they take PathType and FileType , rename them to fromString? and fromString! , then parse? / ! should be a func that taskes string , doesnt take PathType FileType , but derives them from String itself (after normalization)
2. can we improve extendPath? I think its possible to prove that after concatenation the it will give not Option but Path itself without addtional parsings.. I think we need to remove ft from Name bc it is useless
3. appendPath too. also make sure that Path never starts with . like a path from current dir. this will help us to prove that appendPath is safe. GOAL for extendPath appendPath there should be no ? ! variants, but only variants without any ? ! bc I believe its possible to prove safety. Can add more proofs to dataytypes to help.
4. does it make sense to make Pathy a subtype of AnyPath?
5. parse?! should take not string but FilePath, take string should fromString?! should take string, fromFilePath?! FilePath

----

Good catches on both bugs, and the architecture suggestions are the right move. Let me work through these in order.
Bug 1 — yes, real bug. pathSeparators.contains a && pathSeparators.contains b fires on '\\' next to '/' even though they're different characters. Fixing it properly means first pinning down "canonical" (point 2), then comparing against that specific char, not list membership.
Point 3 is the big one. Trying to keep raw strings + globally-scanned invariants (no double-sep, canonical-sep, etc.) and also prove extendPath/appendPath total means inducting over List Char through String.append, which is exactly the kind of proof that's painful to get right blind, with no Lean session to check it in. So I switched representation instead of fighting that:
Path is no longer a validated raw string — it's a List Name (segments) plus a PathType tag, rendered to a FilePath only at the boundary. With that:
"no double separator," "canonical separator," "no leading dot" all become automatic — we only ever insert the separator ourselves, exactly once, between segments. There's nothing left to accidentally double.
extendPath/appendPath become literal List.append, and the one proof obligation (segments = [] → pathKind = .Abs ∧ ft = .Dir, see point 4) discharges via List.append_eq_nil, no string induction needed. Fully total, no ?/!.
This also directly answers point 4: Path pt ft is now defined as a subtype of AnyPath ft ({p : AnyPath ft // p.pathKind = pt}) — AnyPath holds the data, Path just pins down the tag. Same data, one less thing duplicated.
I dropped ft from Name (point 2/your last list) — it was only ever used for the extendPath overload, and the new generic extendPath doesn't need it.
Parsing a raw FilePath/String into this segment form is still genuinely partial (arbitrary external strings can be malformed), so fromFilePath?/fromFilePath! stay Option/panic!, with fromString?! as thin wrappers calling them (point 5).
One real limitation this surfaces, worth flagging explicitly rather than hiding: a relative path with exactly one segment has no representable parent (going up lands on the banned "."), so parentOf?/peel? stay Option — that's inherent to disallowing ., not a shortcut I took.
