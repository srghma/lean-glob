module
public import LSpec
public import NonEmpty.String
public import NonEmpty.List
public import NonEmpty.Aliases.FunctorsAndScalars
public import NonEmpty.List.Upgraders
@[expose] public section

open NonEmpty.String NonEmpty.List
open LSpec SlimCheck Gen

def String.shrinkByRemovingIndividualElements (s : String) : List String :=
  let cs := s.toList
  (List.range cs.length).map (fun i => (cs.eraseIdx i).asString)

def String.shrinkByRemovingSuffixes (s : String) : List String :=
  let cs := s.toList
  (List.range cs.length).reverse.map fun n => (cs.take n).asString

def String.shrink (s : String) : List String := shrinkByRemovingIndividualElements s ++ shrinkByRemovingSuffixes s

end
