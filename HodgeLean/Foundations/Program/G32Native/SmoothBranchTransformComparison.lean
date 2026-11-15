import HodgeLean.Foundations.Program.G32Native.ReducedTransformReducedComparison
import HodgeLean.Foundations.Program.SchoenTowerGeometryDefs
import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.Reduced
import HodgeLean.Ported.Hironaka.Scheme.BlowUp.Transform.Reduced

/-! Identify native reduced transforms with saturation transforms for smooth branches. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- A smooth branch has the same native reduced and saturation strict-transform ideals. -/
theorem g32l4_smooth_branch_strictTransform_eq
    (B : Over (Spec ↧ℂ)) [IsLocallyNoetherian B.left]
    (D K : B.left.IdealSheafData) [Smooth (s2c_subscheme B D).hom] :
    s2c_strictTransform K.blowUpπ D K = D.strictTransform K := by
  letI : Smooth (D.subschemeι ≫ B.hom) :=
    inferInstanceAs (Smooth (s2c_subscheme B D).hom)
  letI : IsReduced D.subscheme :=
    AlgebraicGeometry.SingularCycles.smooth_reduced_integral (D.subschemeι ≫ B.hom)
  letI : IsReduced (D.strictTransform K).subscheme := isReduced_strictTransform_subscheme K D
  exact g32l4_reducedTransform_blowUp_eq_strictTransform D K

end HodgeLean.Foundations.Program
