import HodgeLean.Foundations.Program.G32SelectedRealizationModelPeriod

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

theorem g32y_modelOperator_sum (L : Type) [AddCommGroup L]
    [Module.Finite ℤ L] [Module.Free ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F)
    (Q : LinearMap.BilinForm ℤ L) (hQ : b2_IsRiemannForm L F Q)
    {I : Type*} [Fintype I] (z : I → ℤ) (φ : I → L →+ L) :
    b63g_modelOperator L F hF Q hQ (∑ i, z i • φ i) =
      ∑ i, (z i : ℚ) • b63g_modelOperator L F hF Q hQ (φ i) := by
  classical
  letI := b5_groupObj L F hF Q hQ
  letI : IsIntegral (b5_model L F hF Q).left := b5_integral_aux L F hF Q hQ
  letI := b5_smooth_aux L F hF Q hQ
  letI := b5_projective_aux L F hF Q hQ
  have hh : b63g_modelMap L F hF Q hQ (∑ i, z i • φ i) =
      ∑ i, z i • b63g_modelMap L F hF Q hQ (φ i) := by
    ext l
    simp [b63g_modelMap, map_sum]
  simp only [b63g_modelOperator, hh]
  exact g32y_dualOperator_sum _ z _

end HodgeLean.Foundations.Program
