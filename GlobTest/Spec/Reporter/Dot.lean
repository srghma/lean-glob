module
public import GlobTest.Spec.Core
public import GlobTest.Spec.Reporter.Base

@[expose] public section

namespace GlobTest.Spec.Reporter.Dot

open GlobTest.Spec.Core
open GlobTest.Spec.Reporter.Base

structure DotReporterConfig where
  width : Nat := 80

/-- Dot reporter: one character per item (`.` pass, `!` fail, `,` pending),
wrapping at `width` columns. -/
def dotReporter (cfg : DotReporterConfig := {}) : ReporterBuilder := do
  let count ← IO.mkRef (0 : Nat)
  pure
    { reportItem := fun res => do
        let ch := match res.outcome with
          | .success => green "."
          | .failure _ => red "!"
          | .pending => dim ","
        IO.print ch
        let n ← count.modifyGet fun n => (n + 1, n + 1)
        if cfg.width > 0 && n % cfg.width == 0 then
          IO.println ""
        (← IO.getStdout).flush
    , reportSummary := fun _ => IO.println "" }

end GlobTest.Spec.Reporter.Dot
