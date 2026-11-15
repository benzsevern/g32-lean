import HodgeLean.Adapters.TorusSpineProofs

/-! # The torus spine: frozen specification

For a smooth projective integral complex group object, this file records the map-level agreement
between the S12 torus comparison and the canonical cup product, together with low-dimensional
Betti-rank consequences. The comparison is the one induced by the S12 homeomorphism; no second
torus-cohomology comparison is introduced. HC no distance; AV milestone no distance.
-/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
open HodgeLean.RealDefs

namespace HodgeLean.Adapters

variable (X : Over (Spec ↧ℂ)) [GrpObj X] [IsIntegral X.left]
  [Smooth X.hom] [IsProjective X.hom]

/-- The comparison induced by the S12 uniformization intertwines the canonical cup-wedge map
with the torus cup-wedge map after the induced exterior-power map in degree one.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, Lemma 1.3.1. -/
theorem torusSpine_abelianTorusComparison_cupWedgeMap (m : ℕ) :
    (abelianTorusComparison X m).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap m =
      HodgeLean.Foundations.Singular.cupWedgeMap
          (TopCat.of (UnitAddTorus (Fin (2 * dim X.left)))) m ∘ₗ
        exteriorPower.map m (abelianTorusComparison X 1).toLinearMap :=
  torusSpine_abelianTorusComparison_cupWedgeMap_aux X m

example (m : ℕ) :
    (abelianTorusComparison X m).toLinearMap ∘ₗ (cupProductOf X).cupWedgeMap m =
      HodgeLean.Foundations.Singular.cupWedgeMap
          (TopCat.of (UnitAddTorus (Fin (2 * dim X.left)))) m ∘ₗ
        exteriorPower.map m (abelianTorusComparison X 1).toLinearMap :=
  torusSpine_abelianTorusComparison_cupWedgeMap X m

/-- The complete rational Betti-rank sequence in complex dimension one is `(1, 2, 1)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, Lemma 1.3.1. -/
theorem torusSpine_bettiRanks_g1 (hg : dim X.left = 1) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      Module.finrank ℚ (HQ X 1) = 2 ∧
      Module.finrank ℚ (HQ X 2) = 1 :=
  torusSpine_bettiRanks_g1_aux X hg

example (hg : dim X.left = 1) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      Module.finrank ℚ (HQ X 1) = 2 ∧
      Module.finrank ℚ (HQ X 2) = 1 :=
  torusSpine_bettiRanks_g1 X hg

/-- The complete rational Betti-rank sequence in complex dimension two is `(1, 4, 6, 4, 1)`.
Source: Birkenhake–Lange, *Complex Abelian Varieties*, Lemma 1.3.1. -/
theorem torusSpine_bettiRanks_g2 (hg : dim X.left = 2) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      Module.finrank ℚ (HQ X 1) = 4 ∧
      Module.finrank ℚ (HQ X 2) = 6 ∧
      Module.finrank ℚ (HQ X 3) = 4 ∧
      Module.finrank ℚ (HQ X 4) = 1 :=
  torusSpine_bettiRanks_g2_aux X hg

example (hg : dim X.left = 2) :
    Module.finrank ℚ (HQ X 0) = 1 ∧
      Module.finrank ℚ (HQ X 1) = 4 ∧
      Module.finrank ℚ (HQ X 2) = 6 ∧
      Module.finrank ℚ (HQ X 3) = 4 ∧
      Module.finrank ℚ (HQ X 4) = 1 :=
  torusSpine_bettiRanks_g2 X hg

end HodgeLean.Adapters
