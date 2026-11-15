# g32-lean: a Lean 4 formalization of the G32 paper

Contact: Benjamin Severn, benzsevern@gmail.com

Archived releases: v1.0.1 (documentation update), doi:[10.5281/zenodo.24241039](https://doi.org/10.5281/zenodo.24241039); v1.0, doi:[10.5281/zenodo.24239596](https://doi.org/10.5281/zenodo.24239596). All versions: doi:[10.5281/zenodo.24239595](https://doi.org/10.5281/zenodo.24239595).

This repository contains a Lean 4 formalization of the main results of

> Benjamin Severn, *Algebraicity of Weil classes on abelian sixfolds of Weil type for Q(√−3) with discriminant −2* (G32), final version v0.19, Zenodo, doi:[10.5281/zenodo.24239608](https://doi.org/10.5281/zenodo.24239608).

**Paper version.** The correspondence was established against v0.18 (doi:[10.5281/zenodo.24171563](https://doi.org/10.5281/zenodo.24171563)). The mathematical statements are unchanged in v0.19: v0.19 adds only Section 1.4 (Formal verification, describing this repository), one bibliography entry and a new date, and every numbered statement keeps its number. The complete diff and the line-number mapping are in [docs/correspondence/printed/VERSIONS.md](docs/correspondence/printed/VERSIONS.md).

It is a self-contained snapshot, cut from commit 0ea348972dc8396faee9eef1caa89f9d5908823f of the author's
development repository. It contains exactly the import closure of the final
statements (13,048 modules under `HodgeLean/`), the pinned dependencies, and the build and replay
tooling.

## The final statements

All in namespace `HodgeLean.Foundations.Program` (files under
`HodgeLean/Foundations/Program/G32Native/`):

| Paper | Lean | File |
|---|---|---|
| Theorem A | `g32_c3_final_theoremA` | `G32PaperFinalC3.lean` |
| Theorem B | `g32_c3_final_theoremB`, and `g32_c3_final_theoremB_actual` on the actual powers | `G32PaperFinalC3.lean`, `G32PaperActualPowers.lean` |
| Corollary 8.2, first clause | `g32_c3_final_corollary82_first`, and `g32_c3_final_corollary82_first_of_form_intrinsic` stated from the intrinsic form data | `G32PaperFinalC3.lean`, `G32Corollary82IntrinsicForm.lean` |
| Corollary 8.2, second clause (printed form) | `g32_final_corollary82_second_printed_from_data_pel` | `G32PaperPrintedFromDataPEL.lean` |
| Corollary 8.2, second clause (transfer supplied) | `g32_final_corollary82_second_c3_supplied`, `g32_final_corollary82_second_c3_supplied_actual`, `g32_final_corollary82_second_printed` | `G32PaperFinalC3Supplied.lean`, `G32PaperActualPowers.lean`, `G32PaperPrintedPowers.lean` |
| Polarization dictionary (paper §2) | `G32Native.printed_polarization_dictionary` | `PrintedPolarizationDictionary.lean` |

`g32_c3_final_corollary82_second` is the conditional assembly theorem: it takes the Weil-to-powers
transfer as an explicit hypothesis `hPowers` and is kept for reference. It is not the counterpart of
the printed clause; the transfer-supplied statements above are.

Each statement depends only on the three standard axioms `propext`, `Classical.choice` and
`Quot.sound` (`scripts/Axioms.lean`). The closure contains no `sorry`, `admit`, `axiom`,
`native_decide`, `implemented_by` or `extern`.

## What is claimed, and what is not

- **Claimed:** the Lean statements above are proved from Lean core, Mathlib and the pinned
  HodgeConjecture package, with only the three standard axioms, and each was compared clause by clause
  with the printed statement (`docs/correspondence/correspondence.md`). That comparison went through
  nine rounds of independent review. Where the Lean statement differs from the printed one (for example
  Theorem 9.2 is formalized for sixfolds only), the difference is stated there.
- **Modeling convention MC1.** The printed "effective PEL family defined by (D, T)" (paper lines 688–710)
  is represented by its period domain: the family's members are the polarized abelian varieties
  parametrized by that domain, and its generic Hodge group is the Hodge group at a generic point. The
  Kuga family as a relative abelian scheme over Γ\D is not constructed here. MC1 is stated in
  `docs/correspondence/correspondence.md`.
- **Not claimed:** the Hodge conjecture in general, or any statement beyond those listed. The case study
  of the wider development project is not part of this release.

## Building

Requirements: [elan](https://github.com/leanprover/elan). The toolchain (`leanprover/lean4:v4.35.0-rc4`)
and all dependencies are pinned (`lean-toolchain`, `lake-manifest.json`; Mathlib `1f414401f6`,
HodgeConjecture `2ead713179`).

```
scripts/build.sh
```

This deletes `.lake`, downloads Mathlib's official build cache (Mathlib only; every HodgeLean and
HodgeConjecture module is compiled locally), runs `lake build`, and prints the axiom report.

Measured from an empty cache on a 32-core, 128 GB machine: BUILD_TIME_PLACEHOLDER.

## Kernel replay

`tools/ReplayClosure.lean` re-checks, in the Lean kernel, every constant of every checked module of the
closure (HodgeLean and HodgeConjecture), following `leanchecker`'s replay. Lean core, Mathlib and their
pinned dependencies are trusted; the allowlist is at the top of the file. `scripts/replay.sh` runs it in
40 shards (each a contiguous range of modules; run shards on separate machines in parallel), and the
shard ranges must tile the closure.

At commit `0ea348972d` the replay passed: 101 shard reports, all 13,315 checked modules, 1,065,796
constants, every report agreeing on the commit, source hash, `.olean` hash and tool hash, and a
deliberately corrupted control proof rejected. Summed shard time was 38.1 hours (longest single shard
112 minutes on 2 cores); see `evidence/replay-manifest-0ea348972d.md`.

## Licence

Apache License 2.0; see `LICENSE` and `NOTICE`. Ported trees keep their own licence files and headers.

## Citation

If you use this formalization, cite the paper above and this repository (machine-readable metadata in
`CITATION.cff`):

> Benjamin Severn, *g32-lean: a Lean 4 formalization of the G32 paper*, version 1.0, 2026.
> https://github.com/benzsevern/g32-lean. Contact: Benjamin Severn, benzsevern@gmail.com.
