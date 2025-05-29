import LSpec
import Glob.Data.NonEmptyString

open LSpec SlimCheck Gen

def genNonEmptyString : Gen NonEmptyString := do
  -- generate a non-empty list of characters (at least 1 char)
  let chars ← listOf (pure 'a') -- (chooseChar 'a' 'z')
  return NonEmptyString.fromLChar! chars

def NonEmptyString.shrinkByRemovingIndividualElements (s : NonEmptyString) : List NonEmptyString :=
  let cs := s.toString.toList
  let shrunk := (List.range cs.length).filterMap fun i =>
    let newCs := cs.eraseIdx i
    if h : newCs ≠ [] then
      some (NonEmptyString.fromNELChar newCs h)
    else
      none
  shrunk

def NonEmptyString.shrinkByRemovingSuffixes (s : NonEmptyString) : List NonEmptyString :=
  let cs := s.toString.toList
  let shrunk := (List.range cs.length).reverse.filterMap fun n =>
    let cs' := cs.take n
    if h : cs' ≠ [] then
      some (NonEmptyString.fromNELChar cs' h)
    else
      none
  shrunk

def NonEmptyString.shrink (s : NonEmptyString) : List NonEmptyString :=
  s.shrinkByRemovingIndividualElements ++ s.shrinkByRemovingSuffixes

instance : Shrinkable NonEmptyString := Shrinkable.mk NonEmptyString.shrink
