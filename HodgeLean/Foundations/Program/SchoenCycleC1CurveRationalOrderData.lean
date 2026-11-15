import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter
import Mathlib.RingTheory.DiscreteValuationRing.Basic

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual nonzero curve coefficient has point-indexed signed orders
and local units using its native parameters, so repeated occurrences of
one curve point retain the same signed order. -/
theorem s2e_c1_curve_rational_order_data
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left]
    [SmoothOfRelativeDimension 1 Y.hom] [IsProjective Y.hom]
    (f : Y.left.functionField) (hf : f ≠ 0) :
    ∃ n : ComplexPoint Y → ℤ, ∃ u : ∀ p : ComplexPoint Y, (Y.left.presheaf.stalk p.underlying)ˣ,
      ∀ p, f = algebraMap (Y.left.presheaf.stalk p.underlying) Y.left.functionField
        (u p : Y.left.presheaf.stalk p.underlying) *
        algebraMap (Y.left.presheaf.stalk p.underlying) Y.left.functionField
          (s2e_native_curve_parameter Y p) ^ n p := by
  have h (p : ComplexPoint Y) : ∃ n : ℤ, ∃ u : (Y.left.presheaf.stalk p.underlying)ˣ,
      f = algebraMap (Y.left.presheaf.stalk p.underlying) Y.left.functionField
        (u : Y.left.presheaf.stalk p.underlying) *
        algebraMap (Y.left.presheaf.stalk p.underlying) Y.left.functionField
          (s2e_native_curve_parameter Y p) ^ n := by
    letI := s2e_smooth_curve_point_stalk_dvr Y p
    obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.exists_units_eq_smul_zpow_of_irreducible
      (s2e_native_curve_parameter_irreducible Y p) hf
    exact ⟨n, u, by simpa only [Units.smul_def, Algebra.smul_def] using hu⟩
  choose n u hu using h
  exact ⟨n, u, hu⟩

end HodgeLean.Foundations.Program
