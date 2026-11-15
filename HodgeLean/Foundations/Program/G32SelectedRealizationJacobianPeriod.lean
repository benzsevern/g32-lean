import HodgeLean.Foundations.Program.G32SelectedRealizationMarkedPeriod

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

attribute [local irreducible] b5_model b2_abelianF b5_periodEquiv

set_option maxHeartbeats 400000 in
theorem g32y_jacobian_period_equivalence {c : Fin 10 → ℂ} {g : Fin 13 → b4b_Group}
    (D : b65z_SharedFamily c g) (t : b6t_polydisc c) :
    ∃ e : g32x_L D t ≃+ b2_abelianLattice (g32x_J D t),
      (b3_periodF ℂ (b65z_fibre c D.C t)).map (b2_cplxMap e.toAddMonoidHom) =
        b2_abelianF (g32x_J D t) ∧
      ∀ (φ : g32x_L D t →+ g32x_L D t) x l,
        abelianPeriod (g32x_J D t) (g32x_operator D t φ x) (e l) =
          abelianPeriod (g32x_J D t) x (e (φ l)) := by
  classical
  dsimp only [g32x_J, g32x_grp, g32x_operator]
  let L : Type := g32x_L D t
  let F := b3_periodF ℂ (b65z_fibre c D.C t)
  let hF := b3_isWeightOne (E := ℂ) (C := b65z_fibre c D.C t) (by simp)
  let hQ := b3_intersectionForm_isRiemannForm (E := ℂ) (by simp) (D.Q t) (D.hQ t)
  letI := b5_groupObj L F hF (D.Q t) hQ
  letI : IsIntegral (b5_model L F hF (D.Q t)).left := g32x_integral D t
  letI := b5_smooth_aux L F hF (D.Q t) hQ
  letI := b5_projective_aux L F hF (D.Q t) hQ
  let e := b5_periodEquiv L F hF (D.Q t) hQ
  refine ⟨e, ?_, ?_⟩
  · change F.map (b2_cplxMap e.toAddMonoidHom) = b2_abelianF (b5_model L F hF (D.Q t))
    have hm := b5_period_filtration L F hF (D.Q t) hQ
    simpa only [e, L, F] using hm
  · intro φ x l
    change abelianPeriod (b5_model L F hF (D.Q t))
      (b63g_dualOperator _ (b63g_modelMap L F hF (D.Q t) hQ φ) x) (e l) = _
    rw [g32y_dualOperator_period]
    have he : b63g_modelMap L F hF (D.Q t) hQ φ (e l) = e (φ l) := by
      change e (φ (e.symm (e l))) = e (φ l)
      rw [e.symm_apply_apply]
    exact congrArg (abelianPeriod (b5_model L F hF (D.Q t)) x) he

end HodgeLean.Foundations.Program
