import HodgeLean.Foundations.Program.SchoenCycleC1SignedUniformizerOrderUnique
import HodgeLean.Foundations.Program.SchoenCycleNativeCurveParameter

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Exact rational unit equations in the actual native curve parameter
retain a unique signed order at the specified complex point. -/
theorem s2e_c1_native_curve_order_unique
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left]
    [SmoothOfRelativeDimension 1 Z.hom] [IsProjective Z.hom]
    (p : ComplexPoint Z) (u v : (Z.left.presheaf.stalk p.underlying)ˣ) (n m : ℤ)
    (heq : algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField (u : _) *
        algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField
          (s2e_native_curve_parameter Z p) ^ n =
      algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField (v : _) *
        algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField
          (s2e_native_curve_parameter Z p) ^ m) : n = m := by
  letI := s2e_smooth_curve_point_stalk_dvr Z p
  exact s2e_c1_signed_uniformizer_order_unique
    (algebraMap (Z.left.presheaf.stalk p.underlying) Z.left.functionField)
    (IsFractionRing.injective _ _) (s2e_native_curve_parameter Z p)
    (s2e_native_curve_parameter_irreducible Z p) u v n m heq

end HodgeLean.Foundations.Program
