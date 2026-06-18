# GlobTest spec framework — rspec-style rewrite

A minimal port of purescript-spec / rspec to Lean 4, with parallel execution,
hooks, pluggable reporters, and `lake test` CLI flags.

## Entry point

`GlobTest/Main.lean` now reads:

```lean
def main : IO Unit :=
  runSpecAndExitProcess [consoleReporter] do
    describe "Glob library" do
      GlobSpec.spec
      globRealSpec
```

`runSpecAndExitProcess : List ReporterBuilder → Spec → IO Unit` parses CLI args,
runs the spec, and calls `IO.exit` with `0`/`1`.

## What changed

### `GlobTest/Spec/Core.lean` (rewritten)
- `SpecTree`/`SpecM` are now parameterised by an input type `α` so hooks can
  pass values to spec items. `Spec := SpecM Unit Unit`.
- **Parallelism**: by default every selected `it` runs on its own dedicated task
  (`Task.Priority.dedicated`). Per-item reporter output is serialized through a
  `Std.BaseMutex`, so the *report* stays readable; raw `IO.println` inside a test
  body can still interleave (this is the documented trade-off of parallel logging).
  Sequential mode is used automatically for `--fail-fast`, or force it with
  `--sequential`.
- **Hooks**: `before_`, `after_`, `around_`, `before`, `after`, `around`,
  `beforeWith`, `aroundWith`. They map over the wrapped sub-tree's leaf actions
  and nest.
- **Per-test timeout** via a task + poll loop (`--timeout SECONDS` / `--no-timeout`,
  default 30s).
- **`Reporter`** record + `ReporterBuilder := IO Reporter` (so stateful reporters
  can allocate refs). Events delivered: `start`, `reportItem`, `reportSummary`.
- **CLI** (`parseArgs`): `--example/-e`, `--example-matches/-E`, `--fail-fast`,
  `--only-failures`, `--next-failure/-n`, `--timeout`, `--no-timeout`,
  `--sequential`. `--only-failures` reads/writes `.spec-failures`.

### Reporters (split, minimal) under `GlobTest/Spec/Reporter/`
- `Base.lean` — shared ANSI styling, indentation, `summarize`, `defaultSummary`.
- `Console.lean` — `consoleReporter` (suite headers + ✓/✗/~ lines).
- `Dot.lean` — `dotReporter { width }` (`.`/`!`/`,`).
- `Spec.lean` — `specReporter` (indented tree, numbered failures, ms for slow tests).
- `Tap.lean` — `tapReporter` (Test Anything Protocol).
- `Reporter.lean` re-exports all of them.

### `GlobTest/Spec/Assert.lean` (new)
`assertEq`, `assertBool`, `assertIsEmpty`, `assertIsNotEmpty`, and `withinTempDir`
(runs each test in its own fresh temp directory so the filesystem tests are
parallel-safe).

### `GlobTest/GlobSpec.lean` & `GlobTest/GlobRealSpec.lean` (rewritten)
- `runGlobTests` / `runTests #[...]` converted to `describe`/`it`. Assertion
  bodies are unchanged except that helpers now `throw` on mismatch (so the runner
  records pass/fail) instead of printing.
- **All previously commented-out real-fs tests are restored**: `GlobUnsorted`,
  `CheckPattern`, `GlobWithTilde`, `GlobDirsOnly`, `GlobSafe`, `TestErrFlag`.
  Each is wrapped in `withinTempDir` (replacing the old `let _tmpDir ← IO.currentDir`).

## Examples

```
lake test                          # all tests, parallel, console reporter
lake test -- -e baz.txt            # only tests whose name contains "baz.txt"
lake test -- --fail-fast           # stop at first failure (sequential)
lake test -- -n                    # rerun previous failures, stop at first
lake test -- --timeout 5           # 5s per-test timeout
lake test -- --no-timeout
lake test -- --sequential
```

To swap reporters, change the list:
`runSpecAndExitProcess [specReporter] spec`, `[dotReporter {}]`, `[tapReporter]`,
or combine: `[consoleReporter, tapReporter]`.
