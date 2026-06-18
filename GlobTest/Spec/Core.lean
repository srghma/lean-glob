module
import Init.System.IO

open IO

namespace GlobTest.Spec.Core

mutual
  inductive SpecTree
    | group (name : String) (isOnly : Bool) (children : Array SpecTree)
    | test (name : String) (isOnly : Bool) (action : IO Unit)
    | pending (name : String)
end

abbrev SpecM := StateM (Array SpecTree)

def describe (name : String) (specs : SpecM Unit) : SpecM Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s.push (SpecTree.group name false children)

def describeOnly (name : String) (specs : SpecM Unit) : SpecM Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s.push (SpecTree.group name true children)

def it (name : String) (action : IO Unit) : SpecM Unit :=
  modify fun s => s.push (SpecTree.test name false action)

def itOnly (name : String) (action : IO Unit) : SpecM Unit :=
  modify fun s => s.push (SpecTree.test name true action)

def pending (name : String) : SpecM Unit :=
  modify fun s => s.push (SpecTree.pending name)

def focus (specs : SpecM Unit) : SpecM Unit := do
  let (_, children) := specs.run #[]
  let focusedChildren := children.map fun
    | .group n _ c => .group n true c
    | .test n _ a => .test n true a
    | .pending n => .pending n
  modify fun s => s ++ focusedChildren

partial def SpecTree.hasOnly : SpecTree → Bool
  | .group _ isOnly children => isOnly || children.any hasOnly
  | .test _ isOnly _ => isOnly
  | .pending _ => false

partial def runSpecTree (globalHasOnly : Bool) (ancestorIsOnly : Bool) (indent : String) (t : SpecTree) : IO (Nat × Nat × Nat) := do
  match t with
  | .group name isOnly children =>
    let currentHasOnly := ancestorIsOnly || isOnly
    if globalHasOnly && !currentHasOnly && !t.hasOnly then
      return (0, 0, 0)
    
    IO.println s!"{indent}{name}"
    let mut passed := 0
    let mut failed := 0
    let mut skipped := 0
    for child in children do
      let (p, f, s) ← runSpecTree globalHasOnly currentHasOnly (indent ++ "  ") child
      passed := passed + p
      failed := failed + f
      skipped := skipped + s
    return (passed, failed, skipped)
  | .test name isOnly action =>
    let shouldRun := !globalHasOnly || ancestorIsOnly || isOnly
    if shouldRun then
      try
        action
        IO.println s!"{indent}✅ {name}"
        return (1, 0, 0)
      catch e =>
        IO.println s!"{indent}❌ {name}\n{indent}  {e}"
        return (0, 1, 0)
    else
      return (0, 0, 0)
  | .pending name =>
    let shouldRun := !globalHasOnly || ancestorIsOnly
    if shouldRun then
      IO.println s!"{indent}⏸️ {name} (pending)"
      return (0, 0, 1)
    else
      return (0, 0, 0)

def runSpec (specs : SpecM Unit) : IO UInt32 := do
  let (_, trees) := specs.run #[]
  let globalHasOnly := trees.any SpecTree.hasOnly
  let mut passed := 0
  let mut failed := 0
  let mut skipped := 0
  for t in trees do
    let (p, f, s) ← runSpecTree globalHasOnly false "" t
    passed := passed + p
    failed := failed + f
    skipped := skipped + s
  
  IO.println s!"\nPassed: {passed}, Failed: {failed}, Skipped: {skipped}"
  if failed > 0 then
    return 1
  else
    return 0

def shouldEqual [BEq α] [Repr α] (actual : α) (expected : α) : IO Unit := do
  if !(actual == expected) then
    throw (IO.userError s!"Expected {repr expected}, got {repr actual}")

def shouldBe [BEq α] [Repr α] (actual : α) (expected : α) : IO Unit := shouldEqual actual expected

end GlobTest.Spec.Core
