#!/usr/bin/env bash
set -e

echo "Building all targets..."
lake build

echo "Running tests..."
lake env lean GlobTest/Main.lean
lake env lean TypedPathTests.lean

echo "All tests passed!"
