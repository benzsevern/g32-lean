import HodgeLean.Adapters.CupProductOf
import HodgeLean.Foundations.ProjectivePoint

/-! # Nonzero normalization tests before the supported comparison specification

These tests use only the base. The rescaled point model detects a missing
normalization factor; it does not prove normalization of the sheaf comparison.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 4000
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Foundations
namespace HodgeLean.Adapters

/-- The complex scheme point, with its identity structure map.
Source: the definition of the terminal object of `Over (Spec ↧ℂ)`. -/
abbrev ccm16_point : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))

instance ccm16_pointIntegral : IsIntegral ccm16_point.left :=
  (affine_isIntegral_iff (CommRingCat.of ℂ)).mpr inferInstance
instance ccm16_pointSmooth : Smooth ccm16_point.hom := by
  change Smooth (𝟙 (Spec ↧ℂ)); infer_instance
instance ccm16_pointProjective : IsProjective ccm16_point.hom :=
  isProjective_specComplex_id

example : cupUnit ccm16_point ≠ 0 := cupProductOf_unit_ne_zero ccm16_point
example : cupComparison ccm16_point 0 (cupUnit ccm16_point) =
    Singular.unit (TopCat.of (ComplexPoint ccm16_point)) := cupComparison_unit _
example : (cupProductOf ccm16_point).cup (rfl : 0 + 0 = 0)
    (cupUnit ccm16_point) (cupUnit ccm16_point) = cupUnit ccm16_point :=
  (cupProductOf ccm16_point).one_cup _

/-- A deliberately rescaled comparison on a topological point.
Source: linear scalar multiplication by the rational unit 2. -/
def ccm16_rescaledPointComparison (n : ℕ) :
    AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of PUnit) n ≃ₗ[ℚ]
      AlgebraicTopology.Singular.Cohomology ℚ (TopCat.of PUnit) n :=
  LinearEquiv.smulOfNeZero ℚ _ (2 : ℚ) (by norm_num)

example : ccm16_rescaledPointComparison 0 (Singular.unit (R := ℚ) (TopCat.of PUnit)) =
    (2 : ℚ) • Singular.unit (R := ℚ) (TopCat.of PUnit) := rfl

example : Singular.normalizedEquiv (TopCat.of PUnit) ccm16_rescaledPointComparison
    (Singular.unit (R := ℚ) (TopCat.of PUnit)) (Singular.unit_ne_zero _) 0
    (Singular.unit (R := ℚ) (TopCat.of PUnit)) = Singular.unit (R := ℚ) (TopCat.of PUnit) :=
  Singular.normalizedEquiv_unit _ _ _ _

example : Singular.pointCohomologyZeroEquiv (R := ℚ)
    (Singular.cup (TopCat.of PUnit) (rfl : 0 + 0 = 0)
      (ccm16_rescaledPointComparison 0 (Singular.unit (R := ℚ) (TopCat.of PUnit)))
      (ccm16_rescaledPointComparison 0 (Singular.unit (R := ℚ) (TopCat.of PUnit)))) = (4 : ℚ) := by
  rw [Singular.pointCohomologyZeroEquiv_cup]
  change Singular.pointCohomologyZeroEquiv (R := ℚ) ((2 : ℚ) • Singular.unit (R := ℚ) (TopCat.of PUnit)) *
    Singular.pointCohomologyZeroEquiv (R := ℚ) ((2 : ℚ) • Singular.unit (R := ℚ) (TopCat.of PUnit)) = 4
  rw [Singular.pointCohomologyZeroEquiv_smul_unit]
  norm_num

example : Singular.pointCohomologyZeroEquiv (R := ℚ)
    (ccm16_rescaledPointComparison 0 (Singular.cup (TopCat.of PUnit)
      (rfl : 0 + 0 = 0) (Singular.unit (R := ℚ) (TopCat.of PUnit))
      (Singular.unit (R := ℚ) (TopCat.of PUnit)))) = (2 : ℚ) := by
  rw [Singular.one_cup]
  exact Singular.pointCohomologyZeroEquiv_smul_unit 2

end HodgeLean.Adapters
