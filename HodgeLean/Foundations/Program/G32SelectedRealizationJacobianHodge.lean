import HodgeLean.Foundations.Program.G32SelectedRealizationModelAdjoint
import HodgeLean.Foundations.Program.G32SelectedRealizationJacobianPeriod

noncomputable section
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Papers HodgeLean.Foundations
open scoped TensorProduct CategoryTheory.MonObj Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b65z_SharedFamily.topC b65z_SharedFamily.chartC
  b65z_SharedFamily.manC b65z_SharedFamily.t2C b65z_SharedFamily.compactC
  b65z_SharedFamily.connectedC b65z_SharedFamily.actionC b65z_SharedFamily.fibreChart
  b65z_SharedFamily.fibreMan b65z_SharedFamily.fibreT2 b65z_SharedFamily.fibreCompact
  b65z_SharedFamily.fibreConnected b65z_SharedFamily.totalChart b65z_SharedFamily.totalMan

attribute [local irreducible] b5_model b64d_model_homologyCohomology

set_option maxHeartbeats 400000 in
theorem g32y_jacobian_hodge_comparison {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    ∃ e : (ℂ ⊗[ℤ] g32x_L D t) ≃ₗ[ℂ] (ℂ ⊗[ℚ] HQ (g32x_J D t) 1),
      (b3_periodF ℂ (b65z_fibre c D.C t)).map e.toLinearMap =
        cohomologyHodgePiece (g32x_J D t) 1 (1, 0) ∧
      ∀ a : g32p_G, ∀ x, e (b4_cplxAct ℂ (C := b65z_fibre c D.C t) a x) =
        (g32x_deck D t a).baseChange ℂ (e x) := by
  classical
  let L : Type := g32x_L D t
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  let hF := b3_isWeightOne (E := ℂ) (C := b65z_fibre c D.C t) (by simp)
  let hQ := b3_intersectionForm_isRiemannForm (E := ℂ) (by simp) (D.Q t) (D.hQ t)
  letI := b5_groupObj L F hF (D.Q t) hQ
  letI : IsIntegral (b5_model L F hF (D.Q t)).left := g32x_integral D t
  letI := b5_smooth_aux L F hF (D.Q t) hQ
  letI := b5_projective_aux L F hF (D.Q t) hQ
  let e := b64d_model_homologyCohomology L F hF (D.Q t) hQ
  refine ⟨e, ?_, ?_⟩
  · change F.map e.toLinearMap = cohomologyHodgePiece (b5_model L F hF (D.Q t)) 1 (1, 0)
    have hh := b64d_model_homologyCohomology_F L F hF (D.Q t) hQ
    simpa only [e, L, F, hF, hQ, g32x_J] using hh
  · intro a x
    have hc (v : L) : b4_latticeAct ℂ (C := b65z_fibre c D.C t) a
        (b4_latticeAct ℂ a⁻¹ v) = v := by
      rw [← AddMonoidHom.comp_apply, ← b4_latticeAct_mul (D.hG t), mul_inv_cancel,
        b4_latticeAct_one (D.hG t)]
      rfl
    have hAdj (u v : L) : (D.Q t) (b4_latticeAct ℂ a u) v =
        (D.Q t) u (b4_latticeAct ℂ a⁻¹ v) := by
      have hh := b4_intersectionForm_invariant (by simp) (D.hG t) (D.Q t) (D.hQ t)
        a u (b4_latticeAct ℂ a⁻¹ v)
      rw [hc] at hh
      exact hh
    have hh := g32y_model_comparison_adjoint L F hF (D.Q t) hQ
      (b4_latticeAct ℂ (C := b65z_fibre c D.C t) a) (b4_latticeAct ℂ a⁻¹) hAdj x
    exact hh

end HodgeLean.Foundations.Program
