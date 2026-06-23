module
public import Glob
public import Glob.WF.IO
public import Glob.WF.Tree
public import Init.Data.Repr
public import Init.System.IO
public import Lean
public import GlobTest.GlobSpec
public import GlobTest.GlobRealSpec
public import GlobTest.Spec.Core
public import GlobTest.Spec.Reporter
public import TypedGlobTest.GlobRealSpec

@[expose] public section

open GlobTest.Spec.Core
open GlobTest.Spec.Reporter.Console

def main (args : List String) : IO UInt32 :=
  runSpecAndReturnExitCode args [consoleReporter] do
    describe "Glob library" do
      GlobSpec.spec
      globRealSpec
      typedGlobRealSpec
