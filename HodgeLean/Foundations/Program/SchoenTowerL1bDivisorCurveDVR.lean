import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCurvePoints
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorCodimensionDVR

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The stalk of every complex point on the actual smooth curve is a DVR. -/
theorem s2v_l1b_divisor_curve_point_dvr
    (Z : Over (Spec ↧ℂ)) [IsIntegral Z.left] [Smooth Z.hom]
    (hdim : TopologicalSpace.dim Z.left = 1) (b : ComplexPoint Z) :
    IsDiscreteValuationRing (Z.left.presheaf.stalk b.underlying) := by
  letI : SmoothOfRelativeDimension 1 Z.hom := by
    simpa only [hdim] using
      (inferInstance : SmoothOfRelativeDimension (TopologicalSpace.dim Z.left) Z.hom)
  have hc : IsClosed ({b.underlying} : Set Z.left) :=
    ((pointEquivClosedPoint Z.hom) ⟨b.left, by simp⟩).2
  exact s2v_l1b_divisor_codimension_one_dvr Z b.underlying
    (SmoothOfRelativeDimension.coheight_eq_dimension_of_isClosed
      (f := Z.hom) (d := 1) b.underlying hc)

end HodgeLean.Foundations.Program
