module
public import Lean
public import Lean.Elab.Term
public import Lean.Parser.Term
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
public import Glob.NonWF.Types
public import Glob.NonWF.Normalize

@[expose] public section

open NonEmpty.String NonEmpty.List

--------------------------------------

-- Well-formedness rules as predicates
def canFollow : PatternSegmentNonWF → PatternSegmentNonWF → Prop
  | .doubleStar, .doubleStar => False
  | .doubleStar, .oneStar => False
  | _, _ => True

def isValidSequence : List PatternSegmentNonWF → Prop
  | [] => False
  | [_] => True
  | prev :: next :: rest => canFollow prev next ∧ isValidSequence (next :: rest)

def canFollowDecidable (prev next : PatternSegmentNonWF) : Decidable (canFollow prev next) :=
  match prev, next with
  | .doubleStar, .doubleStar => isFalse (by simp [canFollow])
  | .doubleStar, .oneStar => isFalse (by simp [canFollow])
  | .doubleStar, .lit _ => isTrue (by simp [canFollow])
  | .doubleStar, .regex _ => isTrue (by simp [canFollow])
  | .oneStar, _ => isTrue (by cases next <;> simp [canFollow])
  | .lit _, _ => isTrue (by cases next <;> simp [canFollow])
  | .regex _, _ => isTrue (by cases next <;> simp [canFollow])

instance isValidSequenceDecidable : (segments : List PatternSegmentNonWF) → Decidable (isValidSequence segments)
  | [] => isFalse (by simp [isValidSequence])
  | [_] => isTrue trivial
  | prev :: next :: rest =>
    match canFollowDecidable prev next, isValidSequenceDecidable (next :: rest) with
    | isTrue h₁, isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h, _ => isFalse (by intro ⟨h', _⟩; exact h h')
    | _, isFalse h => isFalse (by intro ⟨_, h'⟩; exact h h')

--------------------------------------

structure PatternValidated : Type where
  pattern : List PatternSegmentNonWF
  valid_sequence : isValidSequence pattern
  deriving Repr
instance : BEq PatternValidated where
  beq a b := a.pattern == b.pattern


instance : Inhabited PatternValidated where
  default := ⟨[.oneStar], by simp [isValidSequence]⟩

open Lean Meta Elab


-- Now the main ToExpr instance for PatternValidated
instance : ToExpr PatternValidated where
  toTypeExpr := mkConst ``PatternValidated
  toExpr pv :=
    let patternExpr := toExpr pv.pattern
    -- Construct a term representing `isValidSequence pv.pattern` using a decidable instance
    let validType := mkApp (mkConst ``isValidSequence) patternExpr
    let validInstance := mkApp (mkConst ``isValidSequenceDecidable) patternExpr
    let validProof := mkDecidableProof validType validInstance
    -- Construct the final PatternValidated.mk expression
    mkApp2 (mkConst ``PatternValidated.mk) patternExpr validProof

inductive PatternValidatedError where
  | invalidEmpty : PatternValidatedError
  | invalidWrongOrdering : PatternValidatedError
  deriving Repr
instance : BEq PatternValidated where
  beq a b := a.pattern == b.pattern


def PatternValidatedError.toHumanReadable : PatternValidatedError → String
  | .invalidEmpty => "Pattern cannot be empty."
  | .invalidWrongOrdering => r#"Pattern doesn't follow rules:
  1. Double stars can follow only * or "foo" (**/** is disallowed).
  2. One stars can follow only * or "foo" (**/* is disallowed)."#

def PatternValidated.mk? (segments : List PatternSegmentNonWF) : Except PatternValidatedError PatternValidated :=
  if h : isValidSequence segments then .ok ⟨segments, h⟩ else .error (if segments = [] then .invalidEmpty else .invalidWrongOrdering)

--------------------------------------

-- rules:
-- ✅ "**/foo/**"
#guard isValidSequence (patternNonWFLax "**/foo/**") = True
#guard (PatternValidated.mk? (patternNonWFLax "**/foo/**")).isOk

-- ⛔ "" (empty list)
#guard isValidSequence (patternNonWFLax "") = False
#guard (PatternValidated.mk? (patternNonWFLax "")).isOk.not

-- ⛔ "**/**" (** cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, .doubleStar]).isOk.not

-- ⛔ "**/*/**" (* cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, .oneStar, .doubleStar]).isOk.not

-- ✅ "foo/*/**"
#guard (PatternValidated.mk? [nes!"foo", .oneStar, .doubleStar]).isOk

-- ✅ "**/foo/*/**" (** can be after *)
#guard (PatternValidated.mk? [.doubleStar, nes!"foo", .oneStar, .doubleStar]).isOk

-- ⛔ "**/foo/**/*" (* cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, nes!"foo", .doubleStar, .oneStar]).isOk.not

-- ⛔ "**/*/foo/**" (* cannot be after **)
#guard (PatternValidated.mk? [.doubleStar, .oneStar, nes!"foo", .doubleStar]).isOk.not

-- ✅ "*/**/foo/**" (** can be after *)
#guard (PatternValidated.mk? [.oneStar, .doubleStar, nes!"foo", .doubleStar]).isOk

-- ✅ "**/foo/**/bar/**"
#guard (PatternValidated.mk? [.doubleStar, nes!"foo", .doubleStar, nes!"bar", .doubleStar]).isOk

-----------------------------

def PatternValidated.patternStrict? (str : String) : Except String PatternValidated :=
  match PatternNonWF'.fromStringStrict str with
  | .error .emptySegment => throw "Did some segment was empty? `foo//bar` should be `foo/bar`"
  | .error (.invalidRegex _) => throw "Regex syntax error in pattern"
  | .ok pat => match (PatternValidated.mk? pat) with
    | .error .invalidEmpty => throw PatternValidatedError.invalidEmpty.toHumanReadable
    | .error .invalidWrongOrdering => throw (s!"Probably You wanted to write {PatternNonWF'.toString $ normalizeSegments pat}\n{PatternValidatedError.invalidWrongOrdering.toHumanReadable}")
    | .ok pat => return pat

def parseVarName (l : List Char) (acc : String) : (String × Bool × Bool × List Char) :=
  match l with
  | '}' :: rest2 => (acc, false, true, rest2)
  | '?' :: '}' :: rest2 => (acc, true, true, rest2)
  | c :: rest2 => parseVarName rest2 (acc.push c)
  | [] => (acc, false, false, [])

partial def checkEnvAndTildeSyntax.loop (chars : List Char) (changed : Bool) : Except String Bool :=
  match chars with
  | [] => pure changed
  | '$' :: '{' :: rest =>
    let (varName, _, closed, remaining) := parseVarName rest ""
    if !closed then
      throw ("Unclosed environment variable syntax: ${" ++ varName)
    else
      checkEnvAndTildeSyntax.loop remaining true
  | _ :: rest => checkEnvAndTildeSyntax.loop rest changed

def checkEnvAndTildeSyntax (chars : List Char) : Except String Bool :=
  match chars with
  | '~' :: '/' :: rest => checkEnvAndTildeSyntax.loop ('/' :: rest) true
  | ['~'] => pure true
  | chars => checkEnvAndTildeSyntax.loop chars false

partial def expandEnvAndTilde.loop (chars : List Char) (result : String) (changed : Bool) : IO (String × Bool) := do
  match chars with
  | [] => pure (result, changed)
  | '$' :: '{' :: rest =>
    let (varName, isOptional, closed, remaining) := parseVarName rest ""
        
    if !closed then
      throw (IO.userError ("Unclosed environment variable syntax: ${" ++ varName))
      
    let val? ← IO.getEnv varName
    match val? with
    | some val => 
      expandEnvAndTilde.loop remaining (result ++ val) true
    | none =>
      if isOptional then
        expandEnvAndTilde.loop remaining result true
      else
        throw (IO.userError ("Environment variable not set: " ++ varName))
  | c :: rest =>
    expandEnvAndTilde.loop rest (result.push c) changed

def expandEnvAndTilde (s : String) : IO (String × Bool) := do
  match s.toList with
  | '~' :: '/' :: rest =>
    let some home ← IO.getEnv "HOME" | throw (IO.userError "HOME environment variable is not set")
    expandEnvAndTilde.loop ('/' :: rest) home true
  | ['~'] =>
    let some home ← IO.getEnv "HOME" | throw (IO.userError "HOME environment variable is not set")
    pure (home, true)
  | chars => expandEnvAndTilde.loop chars "" false

def PatternValidated.patternStrictWithEnvVars_unchecked (str : String) : IO PatternValidated := do
  let (expandedStr, _) ← expandEnvAndTilde str
  let expandedRel : String := if expandedStr.startsWith "/" then (expandedStr.drop 1).toString else expandedStr
  match PatternValidated.patternStrict? expandedRel with
  | .ok pat => pure pat
  | .error err => throw <| IO.userError err

def PatternValidated.patternStrictWithEnvVars? (str : String) : Except String (IO PatternValidated) := do
  let changed ← checkEnvAndTildeSyntax str.toList
  if !changed then
    throw "Use patternStrict instead of patternStrictWithEnvVars for pure patterns without environment variables or tilde."
  pure (PatternValidated.patternStrictWithEnvVars_unchecked str)

def PatternValidated.patternStrictWithEnvVars! (str : String) : IO (IO PatternValidated) := do
  match PatternValidated.patternStrictWithEnvVars? str with
  | .ok ioPat => pure ioPat
  | .error err => throw <| IO.userError err

def PatternValidated.patternStrictIO! (str : String) : IO PatternValidated := do
  match PatternValidated.patternStrict? str with
  | .ok  pat => pure pat
  | .error err => throw <| IO.userError err

end
