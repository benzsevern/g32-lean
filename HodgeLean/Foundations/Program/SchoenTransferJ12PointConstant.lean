import HodgeLean.Foundations.Program.SchoenTransferJ12CurveConstant

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters
namespace HodgeLean.Foundations.Program
attribute [local irreducible] cupProductOf homPullback

/-- Factoring through an actual complex point kills pullback in every positive degree.
Source: cohomology above the dimension of the complex point and actual pullback functoriality. -/
theorem s4_selected_point_constant_pullback_positive
    (A Y : Over (Spec ↧ℂ))
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    [IsIntegral Y.left] [Smooth Y.hom] [IsProjective Y.hom]
    (e : ComplexPoint A) (n : ℕ) (hn : n ≠ 0) :
    homPullback ((Over.homMk Y.hom : Y ⟶ Over.mk (𝟙 (Spec ↧ℂ))) ≫ e) n = 0 := by
  let T : Over (Spec ↧ℂ) := Over.mk (𝟙 (Spec ↧ℂ))
  letI : IsIntegral T.left := by change IsIntegral (Spec ↧ℂ); infer_instance
  letI : Smooth T.hom := by change Smooth (𝟙 (Spec ↧ℂ)); infer_instance
  letI : IsProjective T.hom := by
    change IsProjective (𝟙 (Spec ↧ℂ))
    exact HodgeLean.Foundations.isProjective_specComplex_id
  letI : SmoothOfRelativeDimension 0 T.hom := by
    change SmoothOfRelativeDimension 0 (𝟙 (Spec ↧ℂ)); infer_instance
  letI := j5d_subsingleton_HQ_of_lt T 0 (m := n) (by omega)
  rw [spec_homPullback_comp]
  ext x
  change homPullback (Over.homMk Y.hom : Y ⟶ T) n (homPullback e n x) = 0
  rw [Subsingleton.elim (homPullback e n x) 0, map_zero]

#print axioms s4_selected_point_constant_pullback_positive
end HodgeLean.Foundations.Program
