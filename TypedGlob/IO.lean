module
public import Init.System.IO
public import Lean
public import Glob.NonWF.Types
public import Glob.WF.Types
public import TypedPath.PosixPath
public import TypedPath.PosixPath.IO

@[expose] public section

open NonEmpty.String NonEmpty.List
open IO.FS
open IO.FS (DirEntry Metadata)
open System (FilePath)
open Posix (PosixPath parsePosixPath AnyPosixPath ExpectedPosixPath Config ParseError PosixComponent)
open Posix.IO

def globParseConfig : Posix.Config :=
  { treatTwoOrMoreRepeatingSeparatorsAsOne := true
    allowTrailingSeparator := true
    cwdIsNotAllowedButInputIsCwd := .Throw
    ifParentsNotAllowed_whatToDoIfParentIsInInput := .Throw
    ifRequestedRelButStartsWithSlash := .Throw
    ifRequestedAbsButNoSlash := .Throw
    ifRequestedDirButNoTrailingSlash := .Throw
    ifRequestedFileButTrailingSlash := .Throw }

structure PosixDirWalker (ap : Bool) (pt : PathType) (ac : Bool) where
  root : PosixPath ap pt .Dir ac
  prune : PosixPath false .Rel .Dir false → IO Bool := fun _ => pure false

inductive PosixDirWalkerEntry (ap : Bool) (pt : PathType) (ac : Bool) where
  | file (relPath : PosixPath false .Rel .File false) (md : Metadata)
  | dir (relPath : PosixPath false .Rel .Dir false) (md : Metadata)

def getRelBase (currentRel : Option (PosixPath false .Rel .Dir false)) : (acRel : Bool) × PosixPath false .Rel .Dir acRel :=
  match currentRel with
  | none => ⟨true, PosixPath.cwd⟩
  | some p => ⟨false, p⟩

partial def PosixDirWalker.forInRec {β : Type} {ap : Bool} {pt : PathType} {ac : Bool} {acAbs : Bool}
    (w : PosixDirWalker ap pt ac)
    (currentAbs : PosixPath ap pt .Dir acAbs)
    (currentRel : Option (PosixPath false .Rel .Dir false))
    (init : β)
    (f : PosixDirWalkerEntry ap pt ac → β → IO (ForInStep β)) : IO (ForInStep β) := do
  try
    let entries ← readDirWithMetadata currentAbs
    let mut state := init
    for (entry, md) in entries do
      let isDir := md.type == _root_.IO.FS.FileType.dir
      let comp := entry.fileName  -- already a PosixNormalComponent

      -- Build the next relative path by appending the component (no string parsing)
      let ⟨_, relBase⟩ := getRelBase currentRel

      if isDir then
        match relBase.appendNormalComponent? comp .Dir with
        | some relPathDir =>
          match currentAbs.appendNormalComponent? comp .Dir with
          | some absPathDir =>
            match ← f (.dir relPathDir md) state with
            | .done s => return .done s
            | .yield s =>
              state := s
              if !(← w.prune relPathDir) then
                match ← forInRec w absPathDir (some relPathDir) state f with
                | .done s => return .done s
                | .yield s => state := s
          | none => pure ()
        | none => pure ()
      else
        match relBase.appendNormalComponent? comp .File with
        | some relPathFile =>
          match ← f (.file relPathFile md) state with
          | .done s => return .done s
          | .yield s => state := s
        | none => pure ()
    return .yield state
  catch _ =>
    return .yield init

instance {ap : Bool} {pt : PathType} {ac : Bool} : ForIn IO (PosixDirWalker ap pt ac) (PosixDirWalkerEntry ap pt ac) where
  forIn w init f := do
    match ← PosixDirWalker.forInRec w w.root none init f with
    | .done s => return s
    | .yield s => return s

def getComponents {ap : Bool} {pt : PathType} {ft : _root_.FileType} {ac : Bool} (p : PosixPath ap pt ft ac) : List (PosixComponent ap) :=
  match p with
  | .cwd => []
  | .path comps _ => comps.toList

partial def matchPosixComponents {ap : Bool} (pattern : List PatternSegmentNonWF) (path : List (PosixComponent ap)) : Bool :=
  match pattern, path with
  | [], [] => true
  | [], _ => false
  | PatternSegmentNonWF.doubleStar :: ps, [] => matchPosixComponents ps ([] : List (PosixComponent ap))
  | _ :: _, [] => false
  | PatternSegmentNonWF.doubleStar :: ps, x :: xs =>
      matchPosixComponents ps (x :: xs) || matchPosixComponents (PatternSegmentNonWF.doubleStar :: ps) xs
  | p :: ps, x :: xs =>
      match x with
      | .parent => false
      | .normal _ => p.matchSlice (toString x |>.toSlice) && matchPosixComponents ps xs

def getComponentsFromSum {ap pt ac} (s : Sum (PosixPath ap pt .File ac) (PosixPath ap pt .Dir ac)) : List (PosixComponent ap) :=
  match s with | .inl f => getComponents f | .inr d => getComponents d

def cmpTypedGlobResult (a b : Sum (PosixPath false .Rel .File false) (PosixPath false .Rel .Dir false)) : Bool :=
  getComponentsFromSum a < getComponentsFromSum b

def typedGlobFS {ap pt ac} (initDir : PosixPath ap pt .Dir ac) (pattern : PatternValidated) : IO (Array (Sum (PosixPath false .Rel .File false) (PosixPath false .Rel .Dir false))) := do
  let mut matched := #[]
  for entry in ({ root := initDir } : PosixDirWalker ap pt ac) do
    match entry with
    | .file relPath _ =>
      if matchPosixComponents pattern.pattern (getComponents relPath) then
        matched := matched.push (.inl relPath)
    | .dir relPath _ =>
      if matchPosixComponents pattern.pattern (getComponents relPath) then
        matched := matched.push (.inr relPath)
  return matched.qsort cmpTypedGlobResult

def typedGlobWithDirMark {ap pt ac} (initDir : PosixPath ap pt .Dir ac) (pattern : PatternValidated) : IO (Array (Sum (PosixPath false .Rel .File false) (PosixPath false .Rel .Dir false))) :=
  typedGlobFS initDir pattern

end
