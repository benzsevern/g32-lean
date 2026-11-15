/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import HodgeConjecture.Mathlib.Algebra.Homology.Notation
import HodgeLean.RealDefs.Port.AlgebraicGeometry.Cycle.Component.PointCoclassNormalization
import HodgeLean.RealDefs.Port.SupportNormalization
import HodgeLean.RealDefs.Port.SectionRestriction
import HodgeLean.RealDefs.Port.OpenRestrictedLowest
import HodgeLean.RealDefs.Port.AlgebraicGeometry.Cycle.Support

/-! Ported, with modifications (imports rewritten to this repository's modules, the `module`
header dropped, public/expose section markers removed, and only the supported-class part kept:
the positive-kernel class and the mapping-cone comparison are omitted; the upstream licence and
notice are in `HodgeLean/RealDefs/Port/LICENSE` and `NOTICE`), from upstream's
`Other/AlgebraicGeometry/Cycle/Component/PointClassNormalization.lean` at `2ead713`. The
uniqueness lemmas `cycleComponentSupportedInjectiveClass_normalization` and
`cycleComponentSupportedInjectiveClass_unique` are copied from upstream's
`Other/AlgebraicGeometry/Cycle/FundamentalClass.lean`. -/

/-!
# Positive-kernel point normalization of the actual general cycle class

The comparison target is the old exactly normalized point coclass transported
through the actual relative/supported-injective comparison and the literal
positive supported-kernel inclusion. It is NOT a point branch in the cycle map.
The separate comparison with the legacy ordinary class has its own cone sign.
-/

noncomputable section

set_option maxRecDepth 4000

open CategoryTheory Limits TopologicalSpace Opposite
open AlgebraicTopology.Singular

namespace AlgebraicGeometry.ComplexPoint

variable (X : Over (Spec ↧ℂ))
  [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom] (x : X.left)
  {p : ℕ} (hx : Order.coheight x = p)

/-- Exact smooth-locus normalization, not equality only up to a scalar. -/
@[simp]
theorem cycleComponentSupportedInjectiveClass_normalization :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom
      (cycleComponentSupportedInjectiveClass X x hx) =
    cycleComponentSmoothSupportCoclassSection X x hx :=
  AddEquiv.apply_symm_apply (cycleComponentSupportedClassNormalizationIso X x hx) _

/-- The normalized global extension is unique, by injectivity of the
restriction/purity comparison. This is a theorem, not a supplied existence input. -/
theorem cycleComponentSupportedInjectiveClass_unique
    (a : CycleComponentSupportedCohomology X x p)
    (ha : (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
      cycleComponentSmoothSupportCoclassSection X x hx) :
    a = cycleComponentSupportedInjectiveClass X x hx := by
  apply (cycleComponentSupportedClassNormalizationIso X x hx).injective
  exact ha.trans (cycleComponentSupportedInjectiveClass_normalization X x hx).symm

/-- Actual restriction followed by the cohomology-sheaf comparison is the
restriction of the literal relative sheafification unit. -/
theorem complexSupportInjectiveCohomologySheafIsoRelative_restriction_section
    (S : Closeds (ComplexPoint X)) (n : ℕ)
    {V W : Opens (ComplexPoint X)} (a : W ⟶ V) :
    HomologicalComplex.homologyMap
      (TopCat.Sheaf.sectionComplexRestriction (TopCat.of (ComplexPoint X)) ℤᵘᵖ
        (complexSupportInjectiveComplex X S) a) (n : ℤ) ≫
      TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X S) (n : ℤ) W ≫
      (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.app (op W) =
    (complexSupportInjectiveSectionCohomologyEquiv X S V n).toAddCommGrpIso.hom ≫
      (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X)) S n).app (op V) ≫
      (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X)) S n).obj.map a.op := by
  rw [TopCat.Sheaf.sectionCohomologyToSheafSection_restriction_assoc,
    (complexSupportInjectiveCohomologySheafIsoRelative X S n).hom.hom.naturality,
    complexSupportInjectiveCohomologySheafIsoRelative_section_assoc]

section Point

variable (d : ℕ) [SmoothOfRelativeDimension d X.hom]
  (z : ComplexPoint (Over.mk (cycleComponentι X.left x ≫ X.hom)))

/-- The OLD point coclass on the literal whole-open/full-component pair.
The pair map simply forgets all removed support except the chosen point. -/
def analyticComponentPointRelativeCoclass :
    RelativeCohomology ℚ
      (neighborhoodSupportComplementPair
        ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
        (cycleComponentSupport X x)) (2 * d) :=
  relativeCohomologyMap ℚ (2 * d)
    (neighborhoodSupportToPointPairMap
      ((⊤ : Opens (ComplexPoint X)) : Set (ComplexPoint X))
      (cycleComponentSupport X x) (cycleComponentMap X x z)
      (range_cycleComponentMap_subset X x ⟨z, rfl⟩))
    (analyticPointLocalCoclass X d (cycleComponentMap X x z))

/-- The old point coclass transported through the ACTUAL relative/supported-injective
comparison; this is an explicit comparison target, not the definition of the general class. -/
def analyticComponentPointSupportedInjectiveCoclass :
    (((TopCat.Sheaf.supportEvaluation (TopCat.of (ComplexPoint X)) ⊤).mapHomologicalComplex
      ℤᵘᵖ).obj (complexSupportInjectiveComplex X
        (cycleComponentAnalyticClosedSupport X x))).homology (2 * (d : ℤ)) :=
  (complexSupportInjectiveSectionCohomologyEquiv X
    (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * d)).symm
      (analyticComponentPointRelativeCoclass X x d z)

/-- The comparison target retains exactly the old normalized relative point coclass. -/
@[simp]
theorem analyticComponentPointSupportedInjectiveCoclass_relative :
    complexSupportInjectiveSectionCohomologyEquiv X
      (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * d)
      (analyticComponentPointSupportedInjectiveCoclass X x d z) =
        analyticComponentPointRelativeCoclass X x d z :=
  AddEquiv.apply_symm_apply _ _

/-- Its literal sheafification image is the old point section on the whole ambient open. -/
theorem analyticComponentPointRelativeCoclass_toSheaf :
    (supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * d)).app (op ⊤)
        (analyticComponentPointRelativeCoclass X x d z) =
      analyticPointCoclassSupportSection X d (cycleComponentSupport X x)
        (cycleComponentMap X x z) (range_cycleComponentMap_subset X x ⟨z, rfl⟩) ⊤ := rfl

/-- The old point candidate has the EXACT general smooth-locus section as its
canonical sheaf normalization, using actual maps throughout. -/
theorem analyticComponentPointSupportedInjectiveCoclass_section_normalization
    (hx : Order.coheight x = d) :
    (complexSupportInjectiveCohomologySheafIsoRelative X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)).hom.hom.app
        (op (cycleComponentSmoothSupportAmbientOpen X x))
      (TopCat.Sheaf.sectionCohomologyToSheafSection (TopCat.of (ComplexPoint X))
        (complexSupportInjectiveComplex X (cycleComponentAnalyticClosedSupport X x))
        (2 * (d : ℤ)) (cycleComponentSmoothSupportAmbientOpen X x)
        (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
          (2 * (d : ℤ)) (analyticComponentPointSupportedInjectiveCoclass X x d z))) =
      cycleComponentSmoothSupportCoclassSection X x hx := by
  obtain rfl : dim X.left = d := SmoothOfRelativeDimension.dim_eq X.hom d
  have h := ConcreteCategory.congr_hom
    (complexSupportInjectiveCohomologySheafIsoRelative_restriction_section X
      (cycleComponentAnalyticClosedSupport X x) (2 * dim X.left)
      (homOfLE (show cycleComponentSmoothSupportAmbientOpen X x ≤ ⊤ from le_top)))
        (analyticComponentPointSupportedInjectiveCoclass X x (dim X.left) z)
  refine h.trans ?_
  change (supportRelativeCohomologySheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * dim X.left)).obj.map (homOfLE le_top).op
    ((supportRelativeCohomologyToSheaf (TopCat.of (ComplexPoint X))
      (cycleComponentSupport X x) (2 * dim X.left)).app (op ⊤)
      (complexSupportInjectiveSectionCohomologyEquiv X
        (cycleComponentAnalyticClosedSupport X x) ⊤ (2 * dim X.left)
        (analyticComponentPointSupportedInjectiveCoclass X x (dim X.left) z))) = _
  rw [analyticComponentPointSupportedInjectiveCoclass_relative,
    analyticComponentPointRelativeCoclass_toSheaf]
  exact cycleComponentSmoothSupportCoclassSection_global_point_normalization X x hx z

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
private theorem cycleComponentSupportedInjectiveClass_point_normalization_aux
    (hx : Order.coheight x = d) (a : CycleComponentSupportedCohomology X x d)
    (ha : (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)) a =
        analyticComponentPointSupportedInjectiveCoclass X x d z) :
    (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
      cycleComponentSmoothSupportCoclassSection X x hx := by
  have hnorm :
      (cycleComponentSupportedClassNormalizationIso X x hx).toAddMonoidHom a =
        (complexSupportInjectiveCohomologySheafIsoRelative X
          (cycleComponentAnalyticClosedSupport X x) (2 * d)).hom.hom.app
            (op (cycleComponentSmoothSupportAmbientOpen X x))
          ((cycleComponentSmoothSupportLowestSectionCohomologyComplexIso X x hx).hom
            (HomologicalComplex.homologyMap (cycleComponentSupportSectionRestriction X x)
              (2 * (d : ℤ))
              ((rationalSupportAddEquivSupportedInjectiveHomology X
                (cycleComponentAnalyticClosedSupport X x) (2 * d)) a))) := by
    exact cycleComponentSupportedClassNormalizationIso_apply X x hx a
  rw [hnorm,
    cycleComponentSmoothSupportLowestSectionCohomologyComplexIso,
    TopCat.Sheaf.openRestrictedLowestSectionCohomologyIso_hom,
    ha]
  exact analyticComponentPointSupportedInjectiveCoclass_section_normalization X x d z hx

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The supported component class equals the normalized point class. -/
theorem cycleComponentSupportedInjectiveClass_point_normalization
    (hx : Order.coheight x = d) :
    cycleComponentSupportedInjectiveClass X x hx =
      (rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * d)).symm
        (analyticComponentPointSupportedInjectiveCoclass X x d z) := by
  let a : CycleComponentSupportedCohomology X x d :=
    (rationalSupportAddEquivSupportedInjectiveHomology X
      (cycleComponentAnalyticClosedSupport X x) (2 * d)).symm
      (analyticComponentPointSupportedInjectiveCoclass X x d z)
  symm
  apply cycleComponentSupportedInjectiveClass_unique X x hx a
  have ha :
      (rationalSupportAddEquivSupportedInjectiveHomology X
        (cycleComponentAnalyticClosedSupport X x) (2 * d)) a =
        analyticComponentPointSupportedInjectiveCoclass X x d z := by
    dsimp [a]
    exact AddEquiv.apply_symm_apply _ _
  exact cycleComponentSupportedInjectiveClass_point_normalization_aux X x d z hx a ha

end Point

end AlgebraicGeometry.ComplexPoint

end
