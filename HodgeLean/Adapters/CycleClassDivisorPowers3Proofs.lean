import HodgeLean.Adapters.CycleClassDivisorPowers
import HodgeLean.Adapters.CycleClassDivisorPowers2

/-! # Composed surface divisor-power proof obligations

The surface route combines the preceding small-dimensional corollary with
the algebraicity of top-degree powers.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxRecDepth 2048
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Foundations.Curves
namespace HodgeLean.Adapters

/-- Source: ccm8_hdg_le_span_g2, ccm9_polarization_pow_algebraic, and
torusCohomology_cupProductOf. -/
theorem ccm10_hdg_le_span_g2_of_sq_ne_zero_aux (X : Over (Spec ↧ℂ))
    [GrpObj X] [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (η : HQ X 2) (hne : cupPow X (cupProductOf X) η 2 ≠ 0)
    (h11 : LefschetzOneOneFor X) (hg : dim X.left = 2) :
    ∀ p : ℕ, Hdg^p(X; ℚ) ≤ algebraicCycleClassSpan X p :=
  ccm8_hdg_le_span_g2 X (cupProductOf X) (torusCohomology_cupProductOf X) η
    (ccm9_polarization_pow_algebraic X η 2 hg) hne h11 hg

/-- Source: ccm10_hdg_le_span_g2_of_sq_ne_zero,
ccm9_theta_square_ne_zero, spec_g2_dim_eq, and E_dim. -/
theorem ccm10_hdg_le_span_EE_aux
    (h11 : LefschetzOneOneFor (g3_power E 2)) :
    ∀ p : ℕ, Hdg^p(g3_power E 2; ℚ) ≤ algebraicCycleClassSpan (g3_power E 2) p :=
  ccm10_hdg_le_span_g2_of_sq_ne_zero_aux (g3_power E 2) ccm8_thetaClass
    ccm9_theta_square_ne_zero h11
    (by rw [spec_g2_dim_eq (g3_powerData E 2), E_dim])

end HodgeLean.Adapters
