import LSpec
import Glob.Data.NonEmptyList

open LSpec SlimCheck Gen

def nonEmptyListOf (x : Gen α) : Gen (NonEmptyList α) := return NonEmptyList.cons' (← x) (← listOf x)

-- try removing each element
-- if get [1, 2, 3, 4] -> [[2, 3, 4], [1, 3, 4], [1, 2, 4], [1, 2, 3]]
def NonEmptyList.shrinkByRemovingIndividualElements (xs : NonEmptyList a) : List (NonEmptyList a) := (List.range xs.length).filterMap (λ i => fromList? $ xs.toList.eraseIdx i)

-- try removing each element
-- if get [1, 2, 3, 4] -> [[1, 2, 3], [1, 2], [1], []]
def NonEmptyList.shrinkByRemovingSuffixes (xs : NonEmptyList a) : List (NonEmptyList a) :=
  (List.range xs.length).reverse.filterMap fun n =>
    fromList? (xs.toList.take n)

-- Default
def NonEmptyList.shrink (xs : NonEmptyList a) : List (NonEmptyList a) := NonEmptyList.shrinkByRemovingSuffixes xs ++ NonEmptyList.shrinkByRemovingSuffixes xs
