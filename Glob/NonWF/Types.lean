module
public import Init.System.IO
public import Regex
public import Lean
public import Lean.Data.RBMap
public import Std.Data.HashSet
public import Lean.Data.RBTree
public import Lean.Elab.Term
public import Init.Meta
public import Lean.Parser.Term
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.String.ToExpr
public import NonEmpty.List.ToExpr
meta import NonEmpty.String.ToExpr
meta import NonEmpty.List.ToExpr
public import NonEmpty.List.Upgraders
@[expose] public section

open NonEmpty.String NonEmpty.List
open IO.FS
open IO.FS (DirEntry FileType Metadata)
open System (FilePath)


deriving instance BEq for Regex
-- instance : Ord Regex := ⟨fun _ _ => Ordering.eq⟩
-- instance : Hashable Regex := ⟨fun _ => 0⟩
instance : ToString Regex := ⟨fun _ => "regex"⟩

open Lean in
def myMkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

open Lean in
instance : ToExpr Regex where
  toTypeExpr := mkConst ``Regex
  toExpr re :=
    let nfa := toExpr re.nfa
    let wfType := Expr.app (mkConst ``Regex.NFA.WellFormed) nfa
    let wfInstance := Expr.app (mkConst ``Regex.NFA.decWellFormed) nfa
    let wf := myMkDecidableProof wfType wfInstance
    let maxTag := toExpr re.maxTag
    let optimizationInfo := toExpr re.optimizationInfo
    mkApp5 (mkConst ``Regex.mk) nfa wf maxTag (mkConst ``false) optimizationInfo

inductive PatternSegmentNonWF where
  | doubleStar : PatternSegmentNonWF
  | oneStar : PatternSegmentNonWF
  | lit : NonEmptyString -> PatternSegmentNonWF
  | regex : Regex -> PatternSegmentNonWF
  deriving Inhabited, Repr, BEq, DecidableEq --, Ord, Hashable

instance : Coe NonEmptyString PatternSegmentNonWF where
  coe a := .lit a

open Lean Meta Elab

instance : ToExpr PatternSegmentNonWF where
  toTypeExpr := mkConst ``PatternSegmentNonWF
  toExpr
    | .lit nes => mkApp (mkConst ``PatternSegmentNonWF.lit) (@toExpr _ instToExprNonEmptyString nes)
    | .oneStar => mkConst ``PatternSegmentNonWF.oneStar
    | .doubleStar => mkConst ``PatternSegmentNonWF.doubleStar
    | .regex re => mkApp (mkConst ``PatternSegmentNonWF.regex) (toExpr re)

def PatternSegmentNonWF.toString : PatternSegmentNonWF → String
| .doubleStar => "**"
| .oneStar => "*"
| .lit s => NonEmptyString.toString s
| .regex s => s!"(regex {s})"

instance : ToString PatternSegmentNonWF where
  toString := PatternSegmentNonWF.toString

def globSegmentToRegexString (s : String) : Option String := Id.run do
  let chars := s.toList
  if !chars.any (fun c => c == '?' || c == '*' || c == '[' || c == '{' || c == '\\') then
    return none
  let mut res := "^"
  let mut inBrace := false
  let mut escapeNext := false
  for c in chars do
    if escapeNext then
      res := res ++ c.toString
      escapeNext := false
    else if c == '\\' then
      res := res ++ "\\\\"
      escapeNext := true
    else if c == '?' then
      res := res ++ "."
    else if c == '*' then
      res := res ++ ".*"
    else if c == '{' then
      res := res ++ "("
      inBrace := true
    else if c == ',' && inBrace then
      res := res ++ "|"
    else if c == '}' && inBrace then
      res := res ++ ")"
      inBrace := false
    else if c == '.' || c == '+' || c == '(' || c == ')' || c == '|' || c == '^' || c == '$' then
      res := res ++ "\\" ++ c.toString
    else
      res := res ++ c.toString
  res := res ++ "$"
  return some res

def PatternSegmentNonWF.fromNES (nes : NonEmptyString) : Except Regex.Syntax.Parser.Error PatternSegmentNonWF :=
  match nes.toString with
  | "**" => .ok .doubleStar
  | "*"  => .ok .oneStar
  | _    =>
    match globSegmentToRegexString nes.toString with
    | some reStr =>
      match Regex.parse reStr with
      | Except.ok re => .ok (.regex re)
      | Except.error e => .error e
    | none => .ok (.lit nes)


/--
Match a single pattern segment against a tree dir name.
- `lit s` matches if `s = name`.
- `oneStar` matches any single name.
- `doubleStar` is handled at pattern list level, not here.
- `regex s` parses and matches using lean-regex.
-/
def PatternSegmentNonWF.matchNES (seg : PatternSegmentNonWF) (name : NonEmptyString) : Bool :=
  match seg with
  | .lit s => s == name
  | .oneStar => true
  | .doubleStar => false
  | .regex re => re.test name.toString

def PatternSegmentNonWF.matchS (seg : PatternSegmentNonWF) (name : String) : Bool :=
  match NonEmptyString.fromString? name with
  | none => false
  | some name' => PatternSegmentNonWF.matchNES seg name'

def PatternSegmentNonWF.matchSlice (seg : PatternSegmentNonWF) (name : String.Slice) : Bool :=
  if name.isEmpty then false
  else
    match seg with
    | .lit s => s.toString.toSlice == name
    | .oneStar => true
    | .doubleStar => false
    | .regex re => re.test (ToString.toString name)

open Lean Meta

-- set_option diagnostics true

instance : ToExpr PatternSegmentNonWF where
  toTypeExpr := mkConst ``PatternSegmentNonWF
  toExpr
  | .doubleStar => mkConst ``PatternSegmentNonWF.doubleStar
  | .oneStar    => mkConst ``PatternSegmentNonWF.oneStar
  | .lit s      => mkApp (mkConst ``PatternSegmentNonWF.lit) (toExpr s)
  | .regex re    => mkApp (mkConst ``PatternSegmentNonWF.regex) (toExpr re)

abbrev PatternNonWF' := List PatternSegmentNonWF
abbrev PatternNonWF := NonEmptyList PatternSegmentNonWF

def PatternNonWF'.toString (ps : PatternNonWF') : String := String.intercalate "/" (ps.map PatternSegmentNonWF.toString)

-- "" ok
-- "/" not ok
inductive PatternParseError where
  | invalidRegex (err : Regex.Syntax.Parser.Error)
  | emptySegment
  deriving Repr

def PatternNonWF'.fromStringStrict (s : String) : Except PatternParseError PatternNonWF' :=
  if s == "" then .ok []
  else
    match NonEmpty.List.Traverse.«L/S->L/NES» ((s.split (· == '/')).toList.map (·.toString)) with
    | none => .error .emptySegment
    | some nesList =>
      match nesList.mapM PatternSegmentNonWF.fromNES with
      | .ok res => .ok res
      | .error err => .error (.invalidRegex err)

def PatternNonWF'.fromStringLax (s : String) : PatternNonWF' :=
  (s.split (· == '/')).toList.map (·.toString)
  |> NonEmpty.List.FilterMap.«L/S->L/NES»
  |>.filterMap (fun nes => match PatternSegmentNonWF.fromNES nes with | .ok x => some x | .error _ => none)

def PatternNonWF.toString : PatternNonWF -> String := (PatternNonWF'.toString ·.toList)
def PatternNonWF.fromStringStrict (s : String) : Except PatternParseError PatternNonWF :=
  match PatternNonWF'.fromStringStrict s with
  | .ok l => match NonEmptyList.fromList? l with
    | some p => .ok p
    | none => .error .emptySegment
  | .error e => .error e

end
