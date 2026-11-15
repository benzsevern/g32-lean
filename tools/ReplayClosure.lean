/-
ReplayClosure: kernel replay of a module closure in one environment.

Usage: lake env lean --run ReplayClosure.lean [--corrupt NAME] ROOT [ROOT ...]

It follows `replayFromImports` in the toolchain's `LeanChecker.lean` (Kim Morrison, Sebastian Ullrich;
Apache 2.0), with one change: instead of rebuilding the imported environment once per module, it builds
the environment of the trusted modules once, then replays the constants of every checked module (the most
private module-data part, as `leanchecker` does) into a single kernel environment, in import order, with
`Lean.Kernel.Environment.replay`.

Checked modules: names under `HodgeLean` or `HodgeConjecture`. Trusted (loaded, not replayed): every other
module in the closure (Init, Std, Lean, Mathlib and its dependencies).

`--corrupt NAME` is the negative control: before replay, the value of theorem NAME is replaced by the
value of a different theorem of another type; the run must then fail.
-/
import Lean
import Lean.Replay
open Lean

/-- Trusted side: an explicit allowlist of upstream root namespaces (Lean core and the packages pinned in
`lake-manifest.json`, other than HodgeConjecture). Every other module, whatever its namespace, is checked. -/
def trustedRoots : List Name :=
  [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq, `ProofWidgets, `Plausible, `ImportGraph,
   `LeanSearchClient, `Verso, `Cli, `MD4Lean, `SubVerso, `Illuminate, `LeanChecker, `LeanExport]

def isChecked (m : Name) : Bool :=
  !(trustedRoots.contains m.getRoot)

unsafe def moduleConstants (m : Name) : IO (Array (Name × ConstantInfo)) := do
  let mFile ← findOLean m
  let mut fnames := #[mFile]
  let sFile := OLeanLevel.server.adjustFileName mFile
  if (← sFile.pathExists) then
    fnames := fnames.push sFile
    let pFile := OLeanLevel.private.adjustFileName mFile
    if (← pFile.pathExists) then
      fnames := fnames.push pFile
  let parts ← readModuleDataParts fnames
  match parts[parts.size - 1]? with
  | some (d, _) => return d.constNames.zip d.constants
  | none => throw <| IO.userError s!"failed to read module data of {m}"

unsafe def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let (corrupt, args) : Option Name × List String :=
    match args with
    | "--corrupt" :: n :: rest => (some n.toName, rest)
    | rest => (none, rest)
  let (depRoots, args) : List Name × List String :=
    match args with
    | "--deps" :: ns :: rest => ((ns.splitOn ",").map String.toName, rest)
    | rest => ([], rest)
  let (range?, args) : Option (Nat × Nat) × List String :=
    match args with
    | "--range" :: a :: b :: rest => (some (a.toNat!, b.toNat!), rest)
    | rest => (none, rest)
  let (shard?, roots) : Option (Nat × Nat) × List String :=
    match args with
    | "--shard" :: a :: b :: rest => (some (a.toNat!, b.toNat!), rest)
    | rest => (none, rest)
  let t0 ← IO.monoMsNow
  let rootImports : Array Import := roots.toArray.map fun r => { module := r.toName }
  -- The full closure, in import order (topological), from the header of the full environment.
  let fullEnv ← importModules rootImports {} 0 (loadExts := false)
  let order : Array Name := fullEnv.header.moduleNames
  -- A module is checked if its name is under HodgeLean/HodgeConjecture, or if it imports (transitively) a
  -- checked module: the trusted side must be closed under imports, or checked constants would enter the
  -- base environment unreplayed.
  let mut checkedSet : NameSet := {}
  for h : idx in [0:order.size] do
    let m := order[idx]
    let imps := fullEnv.header.moduleData[idx]!.imports
    if isChecked m || imps.any (fun im => checkedSet.contains im.module) then
      checkedSet := checkedSet.insert m
  let trusted := order.filter (fun m => !checkedSet.contains m)
  let checked := order.filter (fun m => checkedSet.contains m)
  for m in checked do
    if !isChecked m then IO.println s!"REPLAY-CHECKED-BY-IMPORT {m}"
  -- Boundary check: every trusted module has an allowlisted root, and nothing under HodgeLean/HodgeConjecture is trusted.
  for m in trusted do
    if !(trustedRoots.contains m.getRoot) || (`HodgeLean).isPrefixOf m || (`HodgeConjecture).isPrefixOf m then
      IO.println s!"REPLAY-BOUNDARY-ERROR {m} is trusted"
      return 2
  let mut roots0 : NameSet := {}
  for m in trusted do roots0 := roots0.insert m.getRoot
  let mut roots1 : NameSet := {}
  for m in checked do roots1 := roots1.insert m.getRoot
  IO.println s!"REPLAY-BOUNDARY trusted={trusted.size} checked={checked.size} trusted_roots={roots0.toList} checked_roots={roots1.toList}"
  for m in checked do IO.println s!"REPLAY-CHECKED-MODULE {m}"
  -- Independent count: constants of each checked module as visible in the fully loaded environment.
  let mut envCount : Std.HashMap Name Nat := {}
  for (n, _) in fullEnv.constants.map₁.toList do
    if let some idx := fullEnv.getModuleIdxFor? n then
      let mn := fullEnv.header.moduleNames[idx.toNat]!
      if isChecked mn then envCount := envCount.insert mn (envCount.getD mn 0 + 1)
  -- Optional dependency mode. The dependency set is computed from the same terms that are replayed: the
  -- most private module-data part of every checked module (as leanchecker reads it), falling back to the
  -- loaded environment only for trusted constants. Types, values, inductive types with their constructors
  -- and recursors are followed.
  let mut need : NameSet := {}
  let mut replayData : Std.HashMap Name ConstantInfo := {}
  if !depRoots.isEmpty then
    for m in checked do
      for (n, ci) in (← moduleConstants m) do
        replayData := replayData.insert n ci
    let mut stack := depRoots.toArray
    while h : stack.size > 0 do
      let n := stack.back
      stack := stack.pop
      if need.contains n then continue
      need := need.insert n
      let ci? := match replayData[n]? with
        | some ci => some ci
        | none => fullEnv.find? n
      match ci? with
      | some ci =>
        for c in ci.getUsedConstantsAsSet do
          if !need.contains c then stack := stack.push c
        match ci with
        | .inductInfo iv =>
          for c in iv.ctors do stack := stack.push c
          for c in iv.all do stack := stack.push c
          stack := stack.push (n ++ `rec)
        | .ctorInfo cv => stack := stack.push cv.induct
        | .recInfo rv => for c in rv.all do stack := stack.push c
        | _ => pure ()
      | none => IO.println s!"REPLAY-DEPS missing {n}"
    let inChecked := need.toList.filter (fun n => replayData.contains n)
    IO.println s!"REPLAY-DEPS roots={depRoots} dependency_constants={need.size} in_checked_modules={inChecked.length} full_checked_module_constants={replayData.size}"
  -- Sharding (leanchecker semantics): with --range S E, the checked modules before S are loaded from their
  -- compiled files together with the trusted ones, and only checked[S:E] is replayed. Shards S..E covering
  -- [0, checked.size) together replay every checked module once.
  -- --shard k n: contiguous ranges with equal cumulative compiled size (olean bytes) along the order.
  let mut range := range?.getD (0, checked.size)
  if let some (k, n) := shard? then
    let mut sizes : Array Nat := #[]
    for m in checked do
      let f ← findOLean m
      let sz := (← f.metadata).byteSize.toNat
      sizes := sizes.push sz
    let totalSz := sizes.foldl (· + ·) 0
    let mut acc := 0
    let mut bounds : Array Nat := #[0]
    for h : j in [0:sizes.size] do
      acc := acc + sizes[j]
      if bounds.size < n && acc * n ≥ totalSz * bounds.size then
        bounds := bounds.push (j + 1)
    while bounds.size < n + 1 do bounds := bounds.push checked.size
    bounds := bounds.set! n checked.size
    range := (bounds[k]!, bounds[k+1]!)
    IO.println s!"REPLAY-SHARD {k}/{n} bounds={bounds.toList} total_olean_bytes={totalSz}"
  let (rs, re) := range
  let prefixLoaded := checked.extract 0 rs
  let baseList := trusted ++ prefixLoaded
  IO.println s!"REPLAY-RANGE {rs} {re} of {checked.size}; first={checked[rs]?} last={checked[re-1]?}"
  let baseEnv ← importModules (baseList.map fun m => { module := m }) {} 0 (loadExts := false)
  IO.println s!"REPLAY-BASE loaded in {(← IO.monoMsNow) - t0} ms; base modules={baseEnv.header.moduleNames.size}"
  if baseEnv.header.moduleNames.size != baseList.size then
    IO.println s!"REPLAY-BOUNDARY-ERROR base environment has {baseEnv.header.moduleNames.size} modules, expected {baseList.size}"
    return 2
  let mut kenv := baseEnv.toKernelEnv
  let mut total := 0
  let mut i := 0
  -- For the negative control: find a theorem of a different type to borrow a value from.
  let mut donor : Option Expr := none
  for m in checked.extract rs re do
    i := i + 1
    let cs0 ← moduleConstants m
    let cs := if depRoots.isEmpty then cs0 else cs0.filter (fun (n, _) => need.contains n)
    let mut newConstants : Std.HashMap Name ConstantInfo := {}
    for (n, ci) in cs do
      let ci' ← match corrupt, ci with
        | some target, .thmInfo t =>
          if n == target then
            match donor with
            | some v =>
              IO.println s!"REPLAY-CORRUPT replaced the value of {n}"
              pure (ConstantInfo.thmInfo { t with value := v })
            | none => throw <| IO.userError s!"no donor proof found before {n}"
          else
            pure ci
        | _, _ => pure ci
      if corrupt.isSome && donor.isNone then
        if let .thmInfo t := ci then
          if t.type != .const ``True [] then donor := some (.const ``True.intro [])
      newConstants := newConstants.insert n ci'
    try
      kenv ← kenv.replay newConstants
    catch e =>
      let msg := (toString e).replace "\n" " | "
      IO.println s!"REPLAY-FAIL module={m} after {total} constants: {msg}"
      return 1
    total := total + newConstants.size
    -- Completeness: the module data's own constant count (independent of the replay map) must match.
    if depRoots.isEmpty && newConstants.size != cs0.size then
      IO.println s!"REPLAY-COUNT-MISMATCH {m} module_data={cs0.size} replayed={newConstants.size}"
      return 3
    let ec := envCount.getD m 0
    if depRoots.isEmpty && newConstants.size < ec then
      IO.println s!"REPLAY-COUNT-MISMATCH {m} loaded_env={ec} replayed={newConstants.size}"
      return 3
    IO.println s!"REPLAY-MODULE {m} replayed={newConstants.size} module_data={cs0.size} loaded_env={ec}"
    (← IO.getStdout).flush
    if i % 50 == 0 || i == re - rs then
      IO.println s!"REPLAY-PROGRESS {i}/{re - rs} modules (range {rs}..{re}), {total} constants, {(← IO.monoMsNow) - t0} ms, last={m}"
  IO.println s!"REPLAY-OK range={rs}..{re} of {checked.size} replayed_modules={re - rs} constants={total} ms={(← IO.monoMsNow) - t0}"
  return 0
