import HodgeLean.Foundations.Program.SchoenSelectedGeometryDeckBetti
import HodgeLean.Foundations.Program.SchoenSelectedGeometryAlgebraicSquare

noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected

set_option backward.defeqAttrib.useBackward true in
/-- The actual algebraic Abel–Jacobi map respects the selected deck action in degree one. -/
theorem s0_selected_algebraic_deck_betti
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (e : b65z_fibre c D.C t ≃ₜ ComplexPoint X)
    (p₀ : b65z_fibre c D.C t)
    (aj : b65z_fibre c D.C t → b3_Jacobian ℂ (b65z_fibre c D.C t))
    (haj : b3_IsAbelJacobi ℂ (b65z_fibre c D.C t) p₀ aj)
    (hc : Continuous aj) (j : X ⟶ g32x_J D t)
    (hj : ∀ z, Point.map j (e z) =
      b5_theta (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
        (b3_isWeightOne (by simp)) (D.Q t)
        (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)) (aj z))
    (a : g32p_G) (x : HodgeLean.RealDefs.HQ (g32x_J D t) 1) :
    let B := (AlgebraicTopology.Singular.cohomologyMap ℚ 1 (TopCat.ofHom ⟨e, e.continuous⟩)).comp
      (HodgeLean.Adapters.cupComparison X 1).toLinearMap
    B (HodgeLean.Adapters.homPullback j 1 (g32x_deck D t a x)) =
      AlgebraicTopology.Singular.cohomologyMap ℚ 1
        (TopCat.ofHom ⟨fun y : b65z_fibre c D.C t ↦ a⁻¹ • y, (D.hG t a⁻¹).continuous⟩)
        (B (HodgeLean.Adapters.homPullback j 1 x)) := by
  let θ : b3_Jacobian ℂ (b65z_fibre c D.C t) ≃ₜ ComplexPoint (g32x_J D t) := b5_thetaEquiv (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
    (b3_isWeightOne (by simp)) (D.Q t)
    (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t))
  have hs := s0_algebraic_pullback_square (X := X) (Y := g32x_J D t) ⟨e, e.continuous⟩ ⟨θ, θ.continuous⟩
    ⟨aj, hc⟩ j hj 1
  have h₁ := hs (g32x_deck D t a x)
  have h₂ := hs x
  have h₃ := s0_selected_deck_betti D t p₀ aj haj hc a x
  have h₄ := congrArg (AlgebraicTopology.Singular.cohomologyMap ℚ 1
    (TopCat.ofHom ⟨fun y : b65z_fibre c D.C t ↦ a⁻¹ • y, (D.hG t a⁻¹).continuous⟩)) h₂.symm
  exact h₁.trans (h₃.trans h₄)

#print axioms s0_selected_algebraic_deck_betti
end HodgeLean.Foundations.Program
