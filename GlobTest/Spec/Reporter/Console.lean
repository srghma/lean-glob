module
public import GlobTest.Spec.Core
public import GlobTest.Spec.Reporter.Base

@[expose] public section

namespace GlobTest.Spec.Reporter.Console

open GlobTest.Spec.Core
open GlobTest.Spec.Reporter.Base

/-- Console reporter: prints each suite path once (when it changes), then a line
per test under it. Per-item output is already serialized by the runner, so this
stays readable under parallel execution. -/
def consoleReporter : ReporterBuilder := do
  let lastPath ← IO.mkRef (none : Option (Array String))
  let printHeaderIfNeeded (path : Array String) : IO Unit := do
    let prev ← lastPath.get
    unless prev == some path do
      IO.println (bold (magenta (String.intercalate " » " path.toList)))
      lastPath.set (some path)
  pure
    { reportItem := fun res => do
        printHeaderIfNeeded res.path
        match res.outcome with
        | .success =>
          IO.println ("  " ++ green "✓ " ++ dim res.name)
        | .failure err =>
          IO.println ("  " ++ red ("✗ " ++ res.name ++ ":"))
          IO.println ""
          IO.println ("  " ++ red err)
        | .pending =>
          IO.println ("  " ++ cyan ("~ " ++ res.name))
    , reportSummary := defaultSummary }

end GlobTest.Spec.Reporter.Console
