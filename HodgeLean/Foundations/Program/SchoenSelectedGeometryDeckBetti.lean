import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiComparison
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAbelJacobiNaturality
import HodgeLean.Foundations.Program.SchoenSelectedGeometryOperatorComparison

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 512
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected

set_option backward.defeqAttrib.useBackward true in
/-- Abel–Jacobi pullback intertwines the selected deck operator and inverse deck pullback. -/
theorem s0_selected_deck_betti
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (p₀ : b65z_fibre c D.C t)
    (aj : b65z_fibre c D.C t → b3_Jacobian ℂ (b65z_fibre c D.C t))
    (haj : b3_IsAbelJacobi ℂ (b65z_fibre c D.C t) p₀ aj)
    (hc : Continuous aj) (a : g32p_G) (x : HodgeLean.RealDefs.HQ (g32x_J D t) 1) :
    let θ := b5_thetaEquiv (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
      (b3_isWeightOne (by simp)) (D.Q t)
      (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
    let A := AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨aj, hc⟩)
    let T := AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨θ, θ.continuous⟩)
    A (T (HodgeLean.Adapters.cupComparison (g32x_J D t) 1 (g32x_deck D t a x))) =
      AlgebraicTopology.Singular.cohomologyMap ℚ 1
        (TopCat.ofHom ⟨fun y : b65z_fibre c D.C t ↦ a⁻¹ • y, (D.hG t a⁻¹).continuous⟩)
        (A (T (HodgeLean.Adapters.cupComparison (g32x_J D t) 1 x))) := by
  have hm := s0_model_operator_theta_comparison (g32x_L D t)
    (b3_periodF ℂ (b65z_fibre c D.C t)) (b3_isWeightOne (by simp))
    (D.Q t) (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
    (b4_latticeAct ℂ (C := b65z_fibre c D.C t) a⁻¹) (b4_cplxAct_periodF (D.hG t) a⁻¹) x
  have hn := s0_abelJacobi_betti_naturality (C := b65z_fibre c D.C t) (Y := b65z_fibre c D.C t)
    (fun y : b65z_fibre c D.C t ↦ a⁻¹ • y) (D.hG t a⁻¹)
    (b4_latticeAct ℂ (C := b65z_fibre c D.C t) a⁻¹) (b4_latticeAct_isPushforward (D.hG t) a⁻¹)
    (b4_cplxAct_periodF (D.hG t) a⁻¹) p₀ p₀ aj aj haj haj hc hc
  have hm' := congrArg (AlgebraicTopology.Singular.cohomologyMap ℚ 1
    (TopCat.ofHom ⟨aj, hc⟩)) hm
  have hn' := LinearMap.congr_fun hn
    (AlgebraicTopology.Singular.cohomologyMap ℚ 1
      (TopCat.ofHom ⟨b5_thetaEquiv (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
        (b3_isWeightOne (by simp)) (D.Q t)
        (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)),
        (b5_thetaEquiv (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
        (b3_isWeightOne (by simp)) (D.Q t)
        (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))).continuous⟩)
      (HodgeLean.Adapters.cupComparison (g32x_J D t) 1 x))
  simp only [LinearMap.comp_apply] at hn'
  have hfinal := hm'.trans hn'
  have hop : b63g_modelOperator (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
      (b3_isWeightOne (by simp)) (D.Q t)
      (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
      (b4_latticeAct ℂ (C := b65z_fibre c D.C t) a⁻¹) x = g32x_deck D t a x := rfl
  dsimp only
  conv_lhs =>
    arg -1
    arg -1
    arg -1
    rw [← hop]
  exact hfinal

#print axioms s0_selected_deck_betti
end HodgeLean.Foundations.Program
