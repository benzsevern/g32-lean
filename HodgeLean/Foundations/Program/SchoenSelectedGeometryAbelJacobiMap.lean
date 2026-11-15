import HodgeLean.Foundations.Program.G32SelectedRealizationDefs
import HodgeLean.Adapters.GagaMaps

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
/-- The analytic Abel–Jacobi map of a retained fibre algebraizes into its selected period Jacobian. -/
theorem s0_selected_abelJacobi_algebraization
    {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c)
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (e : b65z_fibre c D.C t ≃ₜ ComplexPoint X)
    (he : ContMDiff 𝓘(ℂ, Fin (TopologicalSpace.dim X.left) → ℂ) 𝓘(ℂ, ℂ) ω e.symm)
    (p₀ : b65z_fibre c D.C t) :
    ∃ aj : b65z_fibre c D.C t → b3_Jacobian ℂ (b65z_fibre c D.C t),
      b3_IsAbelJacobi ℂ (b65z_fibre c D.C t) p₀ aj ∧
      ∃ j : X ⟶ g32x_J D t, ∀ x,
        Point.map j (e x) =
          b5_theta (g32x_L D t) (b3_periodF ℂ (b65z_fibre c D.C t))
            (b3_isWeightOne (by simp)) (D.Q t)
            (b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)) (aj x) := by
  let L := g32x_L D t
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  have hF : b2_IsWeightOne L F := b3_isWeightOne (by simp)
  have hQ := b3_intersectionForm_isRiemannForm (by simp) (D.Q t) (D.hQ t)
  letI := b2_latticeMap_discrete F hF
  letI : IsIntegral (b5_model L F hF (D.Q t)).left := b5_integral L F hF (D.Q t) hQ
  letI := b5_smooth L F hF (D.Q t) hQ
  letI := b5_projective L F hF (D.Q t) hQ
  obtain ⟨aj, haj⟩ := b3_exists_abelJacobi (E := ℂ) (by simp) p₀
  have ha := b3_abelJacobi_holomorphic (E := ℂ) (by simp) p₀ aj haj
  have hθ := (b5_theta_holomorphicFunctions L F hF (D.Q t) hQ).1
  letI : SmoothOfRelativeDimension
      (TopologicalSpace.dim (b5_model L F hF (D.Q t)).left) (b5_model L F hF (D.Q t)).hom :=
    inferInstance
  have hθ' : ContMDiff 𝓘(ℂ, b5_V L F)
      𝓘(ℂ, Fin (TopologicalSpace.dim (g32x_J D t).left) → ℂ) ω
      (fun x ↦ (b5_theta L F hF (D.Q t) hQ x : ComplexPoint (g32x_J D t))) := hθ
  obtain ⟨j, hj⟩ := HodgeLean.Adapters.gagam_algebraize X (g32x_J D t)
    (fun z ↦ (b5_theta L F hF (D.Q t) hQ (aj (e.symm z)) : ComplexPoint (g32x_J D t))) (hθ'.comp (ha.comp he))
  refine ⟨aj, haj, j, fun x ↦ ?_⟩
  simpa only [e.symm_apply_apply] using congrFun hj (e x)

#print axioms s0_selected_abelJacobi_algebraization
end HodgeLean.Foundations.Program
