module
import Init.System.IO
public import Std.Sync.Mutex

open IO

/-!
# Spec.Core

A minimal port of purescript-spec / rspec to Lean 4.

Highlights vs the previous version:

* Spec items can run **in parallel** (`runSpecAndExitProcess` /
  `runSpec`). Sequential execution is still available via `Config.parallel := false`.
* **Hooks**: `before_`, `after_`, `around_`, and the value-passing
  `before`, `after`, `around`, `beforeWith`, `aroundWith`. Hooks nest.
* **Reporters** are first class (`Reporter`) and consume an event stream,
  so console / dot / spec / tap reporters can be plugged in:
  `runSpecAndExitProcess [consoleReporter] spec`.
* **CLI args** parsed from `lake test -- ...`:
  `--example` / `-e`, `--example-matches` / `-E`, `--fail-fast`, `--only-failures`,
  `--next-failure` / `-n`, `--timeout`, `--no-timeout`.

Because parallel runs interleave `IO.println` output, reporters buffer
per-item output and flush it atomically once an item finishes, keeping the
report readable even when the work itself overlaps.
-/

namespace Spec.Core

@[expose] public section

/-! ## Spec tree -/

mutual
  /-- A spec item carries an action that receives the value produced by the
  enclosing `before`/`around` hooks (`Unit` when there are none). -/
  inductive SpecTree (α : Type) where
    | group (name : String) (isOnly : Bool) (children : Array (SpecTree α))
    | test (name : String) (isOnly : Bool) (action : α → IO Unit)
    | pending (name : String)
    deriving Nonempty
end

/-- The writer/state monad we accumulate spec items in.

It is parameterised by the input type `α` threaded in from hooks. -/
abbrev SpecM (α : Type) := StateM (Array (SpecTree α))

/-- A full top-level spec produces no input (`Unit`). -/
abbrev Spec := SpecM Unit Unit

/-! ## Building blocks: describe / it / pending -/

def describe (name : String) (specs : SpecM α Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s.push (SpecTree.group name false children)

def describeOnly (name : String) (specs : SpecM α Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s.push (SpecTree.group name true children)

/-- `it` for specs that take an input value from a hook. -/
def itWith (name : String) (action : α → IO Unit) : SpecM α Unit :=
  modify fun s => s.push (SpecTree.test name false action)

def itOnlyWith (name : String) (action : α → IO Unit) : SpecM α Unit :=
  modify fun s => s.push (SpecTree.test name true action)

/-- `it` for the common case where the spec takes no input (`Unit`). -/
def it (name : String) (action : IO Unit) : SpecM Unit Unit :=
  itWith name (fun _ => action)

def itOnly (name : String) (action : IO Unit) : SpecM Unit Unit :=
  itOnlyWith name (fun _ => action)

def pending (name : String) : SpecM α Unit :=
  modify fun s => s.push (SpecTree.pending name)

def focus (specs : SpecM α Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  let focusedChildren := children.map fun
    | .group n _ c => .group n true c
    | .test n _ a => .test n true a
    | .pending n => .pending n
  modify fun s => s ++ focusedChildren

/-! ## Hooks

Hooks transform the action of every leaf inside the wrapped spec. We map
over the tree, replacing the `α → IO Unit` actions.
-/

mutual
  partial def mapAction (f : (α → IO Unit) → (β → IO Unit)) : SpecTree α → SpecTree β
    | .group n o c => .group n o (mapActionArr f c)
    | .test n o a => .test n o (f a)
    | .pending n => .pending n

  partial def mapActionArr (f : (α → IO Unit) → (β → IO Unit)) (c : Array (SpecTree α)) :
      Array (SpecTree β) :=
    c.map (mapAction f)
end

/-- Run `action` before every spec item (no value passed in). -/
def before_ (action : IO Unit) (specs : SpecM α Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run a => do action; run a)

/-- Run `action` after every spec item (even when it throws). -/
def after_ (action : IO Unit) (specs : SpecM α Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run a => do
    try run a finally action)

/-- `around_ withResource spec` wraps each item with setup/teardown. -/
def around_ (around : IO Unit → IO Unit) (specs : SpecM α Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run a => around (run a))

/-- `before` produces a value that is passed to each item. -/
def before (acquire : IO β) (specs : SpecM β Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run _ => do let b ← acquire; run b)

/-- `after` receives the value (from an enclosing `before`/`around`) for teardown. -/
def after (release : β → IO Unit) (specs : SpecM β Unit) : SpecM β Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run b => do
    try run b finally release b)

/-- `around` performs setup, runs the item with the acquired value, then teardown. -/
def around (around : (β → IO Unit) → IO Unit) (specs : SpecM β Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run _ => around run)

/-- `beforeWith` maps the incoming value into a new one. -/
def beforeWith (f : α → IO β) (specs : SpecM β Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run a => do let b ← f a; run b)

/-- `aroundWith` wraps each item, mapping the incoming value. -/
def aroundWith (f : (β → IO Unit) → (α → IO Unit)) (specs : SpecM β Unit) : SpecM α Unit := do
  let (_, children) := specs.run #[]
  modify fun s => s ++ children.map (mapAction fun run a => f run a)

/-! ## `only` detection -/

partial def SpecTree.hasOnly : SpecTree α → Bool
  | .group _ isOnly children => isOnly || children.any hasOnly
  | .test _ isOnly _ => isOnly
  | .pending _ => false

/-! ## Results & events -/

inductive Outcome where
  | success
  | failure (err : String)
  | pending
  deriving Inhabited

structure ItemResult where
  /-- Suite names from the root down to (but not including) the leaf. -/
  path : Array String
  name : String
  outcome : Outcome
  durationMs : Nat
  deriving Inhabited

/-- A reporter is fed each finished item plus a summary at the end.
Per-item printing happens atomically (one `reportItem` call at a time), so
parallel runs stay readable even though completion order is non-deterministic. -/
structure Reporter where
  /-- Called once before any items run. -/
  start : (total : Nat) → IO Unit := fun _ => pure ()
  /-- Called once per finished item, atomically. -/
  reportItem : ItemResult → IO Unit
  /-- Called once after all items finish. -/
  reportSummary : Array ItemResult → IO Unit := fun _ => pure ()

/-- Reporters that need state (e.g. "last printed suite", a counter) are built
in `IO` so they can allocate refs. Stateless reporters use `pure`. -/
abbrev ReporterBuilder := IO Reporter

/-! ## CLI configuration -/

structure Config where
  /-- Substring filter (`--example`/`-e`). -/
  example? : Option String := none
  /-- Regex-ish filter (`--example-matches`/`-E`). We use substring matching of the
  pattern's literal characters to avoid a regex dependency; callers wanting real
  regexes can pre-filter. -/
  exampleMatches? : Option String := none
  failFast : Bool := false
  onlyFailures : Bool := false
  /-- Per-test timeout in milliseconds; `none` means no timeout. -/
  timeoutMs : Option Nat := some 30000
  parallel : Bool := true
  deriving Inhabited

/-- File used to remember which tests failed last run (`--only-failures`). -/
def failuresFile : String := ".spec-failures"

def parseArgs (args : List String) : Config := Id.run do
  let mut cfg : Config := {}
  let mut rest := args
  while !rest.isEmpty do
    match rest with
    | "--example" :: v :: tl | " / -e" :: v :: tl =>
      cfg := { cfg with example? := some v }; rest := tl
    | "--example-matches" :: v :: tl | " / -E" :: v :: tl =>
      cfg := { cfg with exampleMatches? := some v }; rest := tl
    | "--fail-fast" :: tl =>
      cfg := { cfg with failFast := true }; rest := tl
    | "--only-failures" :: tl =>
      cfg := { cfg with onlyFailures := true }; rest := tl
    | "--next-failure" :: tl | " / -n" :: tl =>
      cfg := { cfg with failFast := true, onlyFailures := true }; rest := tl
    | "--timeout" :: v :: tl =>
      cfg := { cfg with timeoutMs := (v.toNat?.map (· * 1000)) }; rest := tl
    | "--no-timeout" :: tl =>
      cfg := { cfg with timeoutMs := none }; rest := tl
    | "--sequential" :: tl =>
      cfg := { cfg with parallel := false }; rest := tl
    | _ :: tl => rest := tl
    | [] => rest := []
  return cfg

/-! ## Flattening the tree into runnable items -/

/-- A leaf paired with the suite path and whether it's selected by `only`. -/
structure Leaf (α : Type) where
  path : Array String
  name : String
  kind : Sum (α → IO Unit) Unit  -- `inl action` = test, `inr ()` = pending
  selected : Bool

partial def flatten (globalHasOnly : Bool) (ancestorOnly : Bool) (path : Array String)
    (t : SpecTree Unit) : Array (Leaf Unit) :=
  match t with
  | .group name isOnly children =>
    let currentOnly := ancestorOnly || isOnly
    if globalHasOnly && !currentOnly && !t.hasOnly then #[]
    else children.foldl (init := #[]) fun acc c =>
      acc ++ flatten globalHasOnly currentOnly (path.push name) c
  | .test name isOnly action =>
    let sel := !globalHasOnly || ancestorOnly || isOnly
    #[{ path, name, kind := .inl action, selected := sel }]
  | .pending name =>
    let sel := !globalHasOnly || ancestorOnly
    #[{ path, name, kind := .inr (), selected := sel }]

/-- Full dotted name used for `--example` filtering. -/
def Leaf.fullName (l : Leaf α) : String :=
  String.intercalate " » " (l.path.toList ++ [l.name])

def matchesFilters (cfg : Config) (failedNames : Array String) (l : Leaf α) : Bool :=
  let full := l.fullName
  let exMatch := match cfg.example? with
    | some s => (full.splitOn s).length > 1
    | none => true
  let eMatch := match cfg.exampleMatches? with
    | some s => (full.splitOn s).length > 1
    | none => true
  let failMatch := !cfg.onlyFailures || failedNames.contains full
  l.selected && exMatch && eMatch && failMatch

/-! ## Running a single leaf -/

/-- Run an action with an optional timeout (ms), returning its outcome and
duration. Uses a task + polling so we don't depend on a particular async API. -/
def runLeaf (cfg : Config) (l : Leaf Unit) : IO ItemResult := do
  match l.kind with
  | .inr () =>
    return { path := l.path, name := l.name, outcome := .pending, durationMs := 0 }
  | .inl action =>
    let start ← IO.monoMsNow
    let task ← IO.asTask (prio := .dedicated) do
      try action (); pure (Outcome.success)
      catch e => pure (Outcome.failure (toString e))
    let outcome ← match cfg.timeoutMs with
      | none =>
        match (← IO.wait task) with
        | .ok o => pure o
        | .error e => pure (Outcome.failure (toString e))
      | some ms =>
        let deadline := start + ms
        let mut res : Option Outcome := none
        while res.isNone do
          if (← IO.hasFinished task) then
            res := some (match task.get with
              | .ok o => o
              | .error e => Outcome.failure (toString e))
          else if (← IO.monoMsNow) > deadline then
            IO.cancel task
            res := some (Outcome.failure s!"timed out after {ms}ms")
          else
            IO.sleep 1
        pure res.get!
    let stop ← IO.monoMsNow
    return { path := l.path, name := l.name, outcome, durationMs := stop - start }

/-! ## The runner -/

def isFailure : Outcome → Bool
  | .failure _ => true
  | _ => false

/-- Run a flattened, filtered list of leaves, dispatching to reporters.
`reporters` are already built (state allocated). Per-item reporting is
serialized through `lock` so parallel output is not interleaved. -/
def runLeaves (cfg : Config) (reporters : List Reporter) (leaves : Array (Leaf Unit)) :
    IO (Array ItemResult) := do
  for r in reporters do r.start leaves.size
  let lock ← Std.BaseMutex.new
  let report (res : ItemResult) : IO Unit := do
    lock.lock
    try
      for r in reporters do r.reportItem res
    finally
      lock.unlock
  let mut results : Array ItemResult := #[]
  if cfg.parallel && !cfg.failFast then
    -- launch everything; report as each finishes, but collect in original order.
    let tasks ← leaves.mapM fun l => IO.asTask (prio := .dedicated) do
      let res ← runLeaf cfg l
      report res
      pure res
    for t in tasks do
      let res ← match (← IO.wait t) with
        | .ok r => pure r
        | .error e => pure { path := #[], name := "<task>", outcome := .failure (toString e), durationMs := 0 }
      results := results.push res
  else
    -- sequential: needed for fail-fast (and when explicitly requested).
    for l in leaves do
      let res ← runLeaf cfg l
      report res
      results := results.push res
      if cfg.failFast && isFailure res.outcome then
        break
  for r in reporters do r.reportSummary results
  return results

/-- Persist the names of failing tests so `--only-failures` works next run. -/
def saveFailures (results : Array ItemResult) : IO Unit := do
  let failed := results.filterMap fun r =>
    if isFailure r.outcome then some (String.intercalate " » " (r.path.toList ++ [r.name])) else none
  unless failed.isEmpty do IO.FS.writeFile failuresFile (String.intercalate "\n" failed.toList)

def loadFailures : IO (Array String) := do
  try
    let content ← IO.FS.readFile failuresFile
    return content.splitOn "\n" |>.filter (!·.isEmpty) |>.toArray
  catch _ => return #[]

/-- Build, filter and run a spec, returning the exit code (0 ok, 1 failure). -/
def runSpecWith (cfg : Config) (reporters : List ReporterBuilder) (spec : Spec) : IO Bool := do
  let (_, trees) := spec.run #[]
  let globalHasOnly := trees.any SpecTree.hasOnly
  let leaves := trees.foldl (init := #[]) fun acc t =>
    acc ++ flatten globalHasOnly false #[] t
  let failedNames ← if cfg.onlyFailures then loadFailures else pure #[]
  let selected := leaves.filter (matchesFilters cfg failedNames)
  let built ← reporters.mapM id
  let results ← runLeaves cfg built selected
  saveFailures results
  let anyFailed := results.any (isFailure ·.outcome)
  return anyFailed

/-- Convenience: parse CLI args from the running process and run. -/
def runSpec (args : List String) (reporters : List ReporterBuilder) (spec : Spec) : IO Bool := do
  let cfg := parseArgs args
  runSpecWith cfg reporters spec

/-- The rspec-style entry point: parse args, run, exit the process. -/
def runSpecAndReturnExitCode (args : List String) (reporters : List ReporterBuilder) (spec : Spec) : IO UInt32 := do
  let failed ← runSpec args reporters spec
  return if failed then 1 else 0

/-! ## Assertions -/

def shouldEqual [BEq α] [Repr α] (actual : α) (expected : α) : IO Unit := do
  if !(actual == expected) then
    throw (IO.userError s!"Expected {repr expected}, got {repr actual}")

def shouldBe [BEq α] [Repr α] (actual : α) (expected : α) : IO Unit := shouldEqual actual expected

/-- `x `shouldReturn` y`: run an action and compare its result. -/
def shouldReturn [BEq α] [Repr α] (actual : IO α) (expected : α) : IO Unit := do
  shouldEqual (← actual) expected

end
end Spec.Core
