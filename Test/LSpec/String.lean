import LSpec
import Glob.Data.NonEmptyString

open LSpec SlimCheck Gen

def String.shrinkByRemovingIndividualElements (s : String) : List String :=
  let cs := s.toList
  (List.range cs.length).map (fun i => (cs.eraseIdx i).asString)

def String.shrinkByRemovingSuffixes (s : String) : List String :=
  let cs := s.toList
  (List.range cs.length).reverse.map fun n => (cs.take n).asString

def String.shrink (s : String) : List String := shrinkByRemovingIndividualElements s ++ shrinkByRemovingSuffixes s
