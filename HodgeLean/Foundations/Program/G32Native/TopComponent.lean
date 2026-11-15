import HodgeLean.RealDefs.PointClassConstant
import HodgeLean.RealDefs.ComplexFundamentalClass

/-! # Nonzero classes of top-codimension components -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program.G32Native

/-- Every top-codimension component has a nonzero absolute class on a smooth integral projective variety. -/
theorem top_component_class_ne_zero
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (d : ℕ) [SmoothOfRelativeDimension d Q.hom]
    (x : Q.left) (hx : Order.coheight x = d) :
    cycleComponentSheafClass Q x hx ≠ 0 := by
  obtain ⟨w, hw⟩ := j5c_exists_complexFundamentalClass Q d
  exact cycleComponentSheafClass_ne_zero_of_fundamentalClass Q d x hx w hw

#print axioms top_component_class_ne_zero
end HodgeLean.Foundations.Program.G32Native
