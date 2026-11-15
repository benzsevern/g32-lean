import HodgeLean.Foundations.Program.G32SelectedRealizationDefs
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiMap
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiBijective
import HodgeLean.Foundations.Program.SchoenSelectedGeometryBettiSquare

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The algebraized Abel–Jacobi map induces a rational degree-one cohomology equivalence. -/
theorem s0_selected_abelJacobi_comparison
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (e : b65z_fibre c D.C t ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm)
    (p₀ : b65z_fibre c D.C t) :
    ∃ aj : b65z_fibre c D.C t → b3_Jacobian ℂ (b65z_fibre c D.C t),
      b3_IsAbelJacobi ℂ (b65z_fibre c D.C t) p₀ aj ∧
      ∃ j : X ⟶ g32x_J D t, Function.Bijective (HodgeLean.Adapters.homPullback j 1) ∧ ∀ x,
        Point.map j (e x) =
          b5_theta (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
            (b3_isWeightOne (by simp)) (D.Q t)
            (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)) (aj x) := by
  obtain ⟨aj, haj, j, hj⟩ := s0_selected_abelJacobi_algebraization D t X e he p₀
  let L := g32x_L D t
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  have hF : b2_IsWeightOne L F := b3_isWeightOne (by simp)
  have hQ := b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)
  letI := b2_latticeMap_discrete F hF
  let θ : b3_Jacobian ℂ (b65z_fibre c D.C t) ≃ₜ ComplexPoint (g32x_J D t) :=
    b5_thetaEquiv L F hF (D.Q t) hQ
  have ha := b3_abelJacobi_holomorphic (E := ℂ) (by simp) p₀ aj haj
  have hb := s0_abelJacobi_rational_pullback_bijective (by simp) p₀ aj haj ha.continuous
  have hs : Function.Bijective (AlgebraicTopology.Singular.cohomologyMap ℚ 1
      (TopCat.ofHom (Point.continuousMap j))) := by
    apply s0_pullback_bijective_of_homeomorph_square e θ
      (TopCat.ofHom ⟨aj, ha.continuous⟩) (TopCat.ofHom (Point.continuousMap j)) 1 _ hb
    ext x : 1
    exact hj x
  refine ⟨aj, haj, j, ?_, hj⟩
  exact (HodgeLean.Adapters.cupComparison X 1).symm.bijective.comp
    (hs.comp (HodgeLean.Adapters.cupComparison (g32x_J D t) 1).bijective)

#print axioms s0_selected_abelJacobi_comparison
end HodgeLean.Foundations.Program
