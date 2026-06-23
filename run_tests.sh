#!/usr/bin/env bash
set -euo pipefail

echo "=== Building libraries ==="

# 1-file libs
echo "--- Building Tree ---"
lake build Tree

echo "--- Building Cutter ---"
lake build Cutter

# many-files libs (root file imports whole tree)
echo "--- Building LSpecExt ---"
lake build LSpecExt

echo "--- Building Spec ---"
lake build Spec

echo "--- Building Glob ---"
lake build Glob

echo "--- Building TypedPath ---"
lake build TypedPath

echo "--- Building TypedGlob ---"
lake build TypedGlob

echo ""
echo "=== Running tests ==="

echo "--- Running GlobTest ---"
lake exe glob_test

echo "--- Running TypedGlobTest ---"
lake exe typed_glob_test

# TypedPathTests is a multi-file lib with type-level tests (no main func).
# Building it is sufficient to verify correctness.
echo "--- Building TypedPathTests (type-level tests) ---"
lake build TypedPathTests

echo ""
echo "All tests passed!"
