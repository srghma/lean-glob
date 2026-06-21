module

@[expose] public section

/-!
# Shared path-parsing helpers

Things both `PosixPath.lean` and `WindowsPath.lean` need.
-/

/-- A version-agnostic splitter that works on any `List Char`. This bypasses
    the breaking changes to `String.split` in Lean 4.27+, same as in your
    original file. Consecutive separators collapse (no empty strings are
    ever produced in the result), which is what makes e.g. `"a//b"` and
    `"a/b"` parse identically. -/
def splitOnPred (cs : List Char) (p : Char → Bool) : List String :=
  let rec loop (acc : List Char) (res : List String) : List Char → List String
    | [] =>
      if acc.isEmpty then res.reverse
      else (String.ofList acc.reverse :: res).reverse
    | c :: rest =>
      if p c then
        if acc.isEmpty then
          loop [] res rest
        else
          loop [] (String.ofList acc.reverse :: res) rest
      else
        loop (c :: acc) res rest
  loop [] [] cs
