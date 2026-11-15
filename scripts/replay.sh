#!/usr/bin/env bash
# Kernel replay of the whole closure, in N shards (default 40), after scripts/build.sh.
# Each shard re-checks every constant of a contiguous range of checked modules
# (HodgeLean and HodgeConjecture) in one kernel environment; Lean core, Mathlib and their
# pinned dependencies are trusted (allowlist in tools/ReplayClosure.lean).
#   scripts/replay.sh            # all shards, sequentially
#   scripts/replay.sh 7          # shard 7 only (run shards on separate machines in parallel)
# A shard prints REPLAY-OK range=S..E on success; ranges from all shards must tile
# [0, total) as printed in REPLAY-BOUNDARY. Negative control:
#   lake env lean --run tools/ReplayClosure.lean --corrupt NAME --shard K N HodgeLean
# must fail (REPLAY-FAIL).
set -euo pipefail
cd "$(dirname "$0")/.."
N=${N:-40}
run() { lake env lean --run tools/ReplayClosure.lean --shard "$1" "$N" HodgeLean; }
if [ $# -ge 1 ]; then run "$1"; else for k in $(seq 0 $((N-1))); do run "$k"; done; fi
