module
public import Spec.Core
public import Spec.Reporter.Base

@[expose] public section

namespace Spec.Reporter.Spec

open Spec.Core
open Spec.Reporter.Base

/-- Spec reporter: indented suite tree with a checkmark / numbered failure / dash
per item, plus speed annotation in ms for slow tests. -/
def specReporter : ReporterBuilder := do
  let numFailures ← IO.mkRef (0 : Nat)
  let lastPath ← IO.mkRef (none : Option (Array String))
  let printSuitesIfNeeded (path : Array String) : IO Unit := do
    let prev ← lastPath.get
    unless prev == some path do
      -- print each suite level (only the parts that changed for tidiness we just
      -- reprint the full path; minimal implementation).
      for i in [0:path.size] do
        IO.println (indent i ++ path[i]!)
      lastPath.set (some path)
  pure
    { reportItem := fun res => do
        printSuitesIfNeeded res.path
        let depth := res.path.size
        match res.outcome with
        | .success =>
          let speed := if res.durationMs > 75 then dim s!" ({res.durationMs}ms)" else ""
          IO.println (indent depth ++ green "✓ " ++ dim res.name ++ speed)
        | .failure _ =>
          let n ← numFailures.modifyGet fun n => (n + 1, n + 1)
          IO.println (indent depth ++ red s!"{n}) {res.name}")
        | .pending =>
          IO.println (indent depth ++ cyan ("- " ++ res.name))
    , reportSummary := defaultSummary }

end Spec.Reporter.Spec
