import LSpec

open LSpec SlimCheck Gen

-- try removing each element
-- if get [1, 2, 3, 4] -> [[2, 3, 4], [1, 3, 4], [1, 2, 4], [1, 2, 3]]
def List.shrinkByRemovingIndividualElements (xs : List a) : List (List a) := (List.range xs.length).map (λ i => xs.eraseIdx i)

-- try removing each element
-- if get [1, 2, 3, 4] -> [[1, 2, 3], [1, 2], [1], []]
def List.shrinkByRemovingSuffixes (xs : List a) : List (List a) :=
  match xs with
  | [] => []
  | _  => (List.range (xs.length)).reverse.map (fun n => xs.take n)

def List.shrink (xs : List a) : List (List a) := List.shrinkByRemovingSuffixes xs ++ List.shrinkByRemovingSuffixes xs
