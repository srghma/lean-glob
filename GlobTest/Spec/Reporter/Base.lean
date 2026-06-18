module
public import GlobTest.Spec.Core

@[expose] public section

namespace GlobTest.Spec.Reporter.Base

open GlobTest.Spec.Core

set_option autoImplicit false

/-! Minimal ANSI styling shared by reporters. -/

def esc : String := "\x1b["
def reset : String := esc ++ "0m"

def code (n : String) (s : String) : String := esc ++ n ++ "m" ++ s ++ reset

def bold (s : String) : String := code "1" s
def dim (s : String) : String := code "2" s
def red (s : String) : String := code "31" s
def green (s : String) : String := code "32" s
def yellow (s : String) : String := code "33" s
def magenta (s : String) : String := code "35" s
def cyan (s : String) : String := code "36" s

def indent (depth : Nat) : String := String.ofList (List.replicate (depth * 2) ' ')

def pluralize (s : String) (n : Nat) : String := if n == 1 then s else s ++ "s"

structure Summary where
  passed : Nat := 0
  failed : Nat := 0
  pending : Nat := 0

def summarize (results : Array GlobTest.Spec.Core.ItemResult) : Summary :=
  results.foldl (init := {}) fun acc r =>
    match r.outcome with
    | .success => { acc with passed := acc.passed + 1 }
    | .failure _ => { acc with failed := acc.failed + 1 }
    | .pending => { acc with pending := acc.pending + 1 }

/-- Default summary block reused by the console/spec reporters. -/
def defaultSummary (results : Array GlobTest.Spec.Core.ItemResult) : IO Unit := do
  let s := summarize results
  let total := s.passed + s.failed
  IO.println ""
  IO.println (bold "Summary")
  let amount := s!"{s.passed}/{total} {pluralize "test" total} passed"
  IO.println (if s.failed > 0 then red amount else dim amount)
  if s.pending > 0 then
    IO.println (yellow s!"{s.pending} {pluralize "test" s.pending} pending")
  IO.println ""

end GlobTest.Spec.Reporter.Base
