module
public import Spec.Core
public import Spec.Reporter
public import TypedGlobTest.GlobRealSpec

@[expose] public section

open Spec.Core
open Spec.Reporter.Console

def main (args : List String) : IO UInt32 :=
  runSpecAndReturnExitCode args [consoleReporter] do
    typedGlobRealSpec
