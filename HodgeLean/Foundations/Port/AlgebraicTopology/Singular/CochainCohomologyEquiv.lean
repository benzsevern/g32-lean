/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.CochainCohomology

/-! Ported, with modifications (imports rewritten to this repository’s modules, the `module`
header dropped, public/expose section markers removed; the upstream licence and notice are in
this directory’s `LICENSE` and `NOTICE`), from upstream’s `Other/AlgebraicTopology/Singular/CochainCohomologyEquiv.lean`
at `2ead713`. -/

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicTopology.Singular

variable (R : Type u) [CommRing R] (X : TopCat.{u})

/-- The short-complex model computes singular cohomology: the degree-`n` short complex of the
singular cochain complex is the reversed dual of the degree-`n` short complex of the singular
chain complex. -/
def cochainCohomologyEquiv (n : ℕ) :
    CochainCohomology R X n ≃ₗ[R] Cohomology R X n :=
  (ShortComplex.homologyMapIso (HomologicalComplex.linearDualCochainComplexScIso
    (SingularChainComplex R X) n)).toLinearEquiv.symm

end AlgebraicTopology.Singular
