module
public import GlobTest.Spec.Core
public import GlobTest.Spec.Reporter.Base

@[expose] public section

namespace GlobTest.Spec.Reporter.Tap

open GlobTest.Spec.Core
open GlobTest.Spec.Reporter.Base

/-- Strip `#` from titles so they're TAP-safe. -/
def escTitle (s : String) : String := s.replace "#" ""

/-- Prefix every line of a message so it reads as a TAP diagnostic. -/
def escMsg (s : String) : String :=
  String.intercalate "\n" ((s.splitOn "\n").map ("  " ++ ·))

/-- TAP reporter (Test Anything Protocol). -/
def tapReporter : ReporterBuilder := do
  let n ← IO.mkRef (1 : Nat)
  pure
    { start := fun total => IO.println s!"1..{total}"
    , reportItem := fun res => do
        let i ← n.modifyGet fun i => (i, i + 1)
        let title := escTitle (String.intercalate " » " (res.path.toList ++ [res.name]))
        match res.outcome with
        | .success => IO.println s!"ok {i} {title}"
        | .pending => IO.println s!"ok {i} {title} # SKIP -"
        | .failure err =>
          IO.println s!"not ok {i} {title}"
          IO.println (escMsg err)
    , reportSummary := fun results => do
        let s := summarize results
        IO.println s!"# tests {s.failed + s.passed + s.pending}"
        IO.println s!"# pass {s.passed + s.pending}"
        IO.println s!"# fail {s.failed}" }

end GlobTest.Spec.Reporter.Tap
