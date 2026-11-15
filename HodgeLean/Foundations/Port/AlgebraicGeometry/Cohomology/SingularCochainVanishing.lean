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

import HodgeLean.Foundations.Port.AlgebraicTopology.Singular.Sheaf.CochainSubdivision

import HodgeLean.Foundations.Port.AlgebraicGeometry.Cohomology.GlobalSections


/-! Ported, with modifications (imports rewritten to this repository's modules, the `module`
header dropped, public/expose section markers removed; the upstream licence and notice are in
this directory's `LICENSE` and `NOTICE`), from upstream's `Other/AlgebraicGeometry/Cohomology/SingularCochainVanishing.lean`
at `2ead713`. -/

/-!
# Singular cohomology and global sections

Lemmas about the definitions in
`HodgeConjecture.Lemmas.AlgebraicGeometry.Cohomology.GlobalSections`.
-/

noncomputable section

open CategoryTheory Limits TopologicalSpace

namespace AlgebraicTopology.Singular.HereditarilyParacompact

/-- Every positive sheaf-cohomology class of every term of the rational singular-cochain
resolution vanishes on a hereditarily paracompact Hausdorff space. -/
theorem rationalSingularCochainTerm_cohomology_succ_eq_zero
    (Y : TopCat.{0}) [T2Space Y] [∀ U : Opens Y, ParacompactSpace U]
    (p q : ℕ) (x : Abelian.Ext
      𝓒(Y; ULift.{0} ℤ)
      (AlgebraicTopology.Singular.singularCochainSheaf ℚ Y p) (q + 1)) :
    x = 0 :=
  AlgebraicTopology.Singular.singularCochainSheaf_cohomology_succ_eq_zero p q x

end AlgebraicTopology.Singular.HereditarilyParacompact
