import HodgeLean.Foundations.Program.SchoenSelectedGeometryThetaExponential
import HodgeLean.Adapters.DegreeOneLattice
import HodgeLean.Foundations.Program.SchoenSelectedGeometryThetaLoops
import HodgeLean.Foundations.Program.SchoenSelectedGeometryTorusLines
import HodgeLean.Foundations.Program.SchoenSelectedGeometryTorusOperator

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters
open scoped Manifold ContDiff TensorProduct CategoryTheory.MonObj
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The theta identification intertwines the selected lattice operator with torus pullback. -/
theorem s0_model_operator_theta_comparison
    (L : Type) [AddCommGroup L] [Module.Finite ℤ L] [Module.Free ℤ L]
    (F : Submodule ℂ (ℂ ⊗[ℤ] L)) (hF : b2_IsWeightOne L F)
    (Q : LinearMap.BilinForm ℤ L) (hQ : b2_IsRiemannForm L F Q)
    (φ : L →+ L) (hφ : F ≤ F.comap (b2_cplxMap φ)) :
    letI := b5_groupObj L F hF Q hQ
    letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
    letI := b5_smooth L F hF Q hQ
    letI := b5_projective L F hF Q hQ
    ∀ x : HodgeLean.RealDefs.HQ (b5_model L F hF Q) 1,
      AlgebraicTopology.Singular.cohomologyMap ℚ 1
          (TopCat.ofHom ⟨b5_thetaEquiv L F hF Q hQ, (b5_thetaEquiv L F hF Q hQ).continuous⟩)
          (cupComparison (b5_model L F hF Q) 1 (b63g_modelOperator L F hF Q hQ φ x)) =
        AlgebraicTopology.Singular.cohomologyMap ℚ 1
          (TopCat.ofHom ⟨b2_torusHom F F φ hφ, b2t_torusHom_continuous F F φ hφ⟩)
          (AlgebraicTopology.Singular.cohomologyMap ℚ 1
            (TopCat.ofHom ⟨b5_thetaEquiv L F hF Q hQ, (b5_thetaEquiv L F hF Q hQ).continuous⟩)
            (cupComparison (b5_model L F hF Q) 1 x)) := by
  letI := b5_groupObj L F hF Q hQ
  letI : IsIntegral (b5_model L F hF Q).left := b5_integral L F hF Q hQ
  letI := b5_smooth L F hF Q hQ
  letI := b5_projective L F hF Q hQ
  intro x
  let e := b5_thetaEquiv L F hF Q hQ
  let v : ContinuousMap (b2_torus L F) (b2_torus L F) :=
    ⟨b2_torusHom F F φ hφ, b2t_torusHom_continuous F F φ hφ⟩
  let k := (⟨e, e.continuous⟩ : ContinuousMap _ _).comp (v.comp ⟨e.symm, e.symm.continuous⟩)
  have hk : ∀ z, k (b5_theta L F hF Q hQ z) = b5_theta L F hF Q hQ (b2_torusHom F F φ hφ z) := by
    intro z
    change e (v (e.symm (e z))) = e (v z)
    rw [e.symm_apply_apply]
  have hm := s0_model_torus_operator L F hF Q hQ φ hφ k hk x
  have hc := congrArg (cupComparison (b5_model L F hF Q) 1) hm
  simp only [LinearEquiv.apply_symm_apply] at hc
  have hs : TopCat.ofHom ⟨e, e.continuous⟩ ≫ TopCat.ofHom k =
      TopCat.ofHom v ≫ TopCat.ofHom ⟨e, e.continuous⟩ := by
    ext z : 1
    change e (v (e.symm (e z))) = e (v z)
    rw [e.symm_apply_apply]
  rw [← hc, ← LinearMap.comp_apply, ← AlgebraicTopology.Singular.cohomologyMap_comp,
    hs, AlgebraicTopology.Singular.cohomologyMap_comp, LinearMap.comp_apply]

#print axioms s0_model_operator_theta_comparison
end HodgeLean.Foundations.Program
