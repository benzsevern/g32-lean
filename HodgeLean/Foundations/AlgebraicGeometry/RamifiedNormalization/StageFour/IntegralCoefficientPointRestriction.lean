import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.IntegralClosureChartPoints

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Restricting an original integral evaluation to its base ring retains the actual complex point and every coefficient value. -/
theorem integral_coefficient_point_restriction_evaluation
    {A L : Type} [CommRing A] [Field L] [Algebra ℂ A] [Algebra A L]
    [Algebra ℂ L] [IsScalarTower ℂ A L]
    (ev : integralClosure A L →ₐ[ℂ] ℂ) (a : A) :
    ComplexPoint.affineSpecEquiv A
      (ComplexPoint.affineSpecComplexPointMap (IsScalarTower.toAlgHom ℂ A (integralClosure A L))
        ((ComplexPoint.affineSpecEquiv (integralClosure A L)).symm ev)) a =
      ev (algebraMap A (integralClosure A L) a) := by
  rw [ComplexPoint.affineSpecEquiv_affineSpecComplexPointMap, Equiv.apply_symm_apply]
  rfl

end AlgebraicGeometry.RamifiedNormalization.StageFour
