import HodgeLean.Foundations.Program.TorusAlgebraization

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The selected theta cover is the exponential of its selected period derivative. -/
theorem s0_theta_cover_exponential
    (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F)
    (Q : LinearMap.BilinForm ℤ L) (hQ : b2_IsRiemannForm L F Q) :
    letI := b5_groupObj L F hF Q hQ
    letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
    letI := b5_smooth L F hF Q hQ
    letI := b5_projective L F hF Q hQ
    ∀ v : b5_V L F, b5_thetaCover L F hF Q hQ v =
      (complexExponential (b5_model L F hF Q) (TopologicalSpace.dim (b5_model L F hF Q).left)
        (b5_periodDerivative L F hF Q hQ v)).toMul := by
  letI := b5_groupObj L F hF Q hQ
  letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
  letI := b5_smooth L F hF Q hQ
  letI := b5_projective L F hF Q hQ
  letI := b2_latticeMap_discrete F hF
  letI : IsCommMonObj (b5_model L F hF Q) := b5_commutative L F hF Q hQ
  have hθP := b56_cover_of _ _ (b5_theta_descent L F hF Q hQ)
  intro v
  exact b56_thetaCover_eq_exp (b5_evaluation_irrelevant L F hF Q hQ)
    (b5_thetaCover L F hF Q hQ) (fun z ↦ rfl)
    (b56_bpf_of (b5_Lcube_basepointFree L F hF Q hQ))
    (b5_theta L F hF Q hQ) hθP _ (b5_group L F hF Q hQ).1
    (b5_group L F hF Q hQ).2.1 v

#print axioms s0_theta_cover_exponential
end HodgeLean.Foundations.Program
