import HodgeLean.Foundations.Program.SchoenTransferJ12CurvePowerCoordinateZero

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- A curve endomorphism factoring through an actual complex point has zero H1 pullback. -/
theorem s4_selected_curve_constant_pullback
    (Y : Over (Spec ↧ℂ)) [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (p : ComplexPoint Y) :
    homPullback ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ p) 1 = 0 := by
  let T : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
  letI : IsIntegral T.left := by change IsIntegral (Spec ↧ℂ); infer_instance
  letI : Smooth T.hom := by change Smooth (𝟙 (Spec ↧ℂ)); infer_instance
  letI : IsProjective T.hom := by
    change IsProjective (𝟙 (Spec ↧ℂ))
    exact HodgeLean.Foundations.isProjective_specComplex_id
  letI : SmoothOfRelativeDimension 0 T.hom := by
    change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ)); infer_instance
  letI := j5d_subsingleton_HQ_of_lt T 0 (m := 1) (by omega)
  rw [spec_homPullback_comp]
  ext x
  change homPullback (Over.homMk Y.hom : Y ⟶ T) 1 (homPullback p 1 x) = 0
  rw [Subsingleton.elim (homPullback p 1 x) 0, map_zero]

#print axioms s4_selected_curve_constant_pullback
end HodgeLean.Foundations.Program
