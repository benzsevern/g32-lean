#!/usr/bin/env bash
# Build from an empty cache. Only Mathlib's official build cache is downloaded; every
# HodgeLean and HodgeConjecture module is compiled locally.
set -euo pipefail
cd "$(dirname "$0")/.."
rm -rf .lake
lake exe cache get          # Mathlib's official cache (mathlib only)
time lake build             # default target HodgeLean: the closure of the final statements
lake env lean scripts/Axioms.lean
