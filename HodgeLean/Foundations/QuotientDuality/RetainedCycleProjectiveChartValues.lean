import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationProjection
import HodgeLean.Foundations.Program.SchoenCycleProjectiveChartPoints

/-! Coordinate evaluation for the projective charts used by finite projections. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial HomogeneousLocalization
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
open scoped TensorProduct
namespace HodgeLean.Foundations.QuotientDuality

/-- Chart evaluation represents the specified homogeneous vector in the projection atlas.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_projective_chart_evaluation_point {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    Spec.map (CommRingCat.ofHom (s2e_standardProjectiveChartEvaluation v i hi).toRingHom) ≫
      a3m_Pnκ n i = vectorToProjectiveSpace v (vector_ne_zero_of_coordinate v i hi) := by
  let φ := s2e_standardProjectiveChartEvaluation v i hi
  unfold a3m_Pnκ
  apply pullback.hom_ext
  · change (_ ≫ _) ≫ ProjectiveSpace.toBase _ _ =
      vectorToProjectiveSpace v _ ≫ ProjectiveSpace.toBase _ _
    rw [vectorToProjectiveSpace_toBase]
    unfold ProjectiveSpace.toBase
    erw [Category.assoc, a3m_prodChart_fst, Category.comp_id,
      ← Spec.map_comp, ← Spec.map_id]
    congr 1
    ext c
    exact φ.commutes c
  · erw [Category.assoc, a3m_prodChart_snd, ← Category.assoc, ← Spec.map_comp,
      vectorToProjectiveSpace_toProj,
      chartIntegralProj_eq_chartIntegralProjAt v (vector_ne_zero_of_coordinate v i hi) i hi]
    unfold chartIntegralProjAt
    congr 2
    ext r
    change φ ((1 : ℂ) ⊗ₜ[ℤ] r) = awayCoordinateEvaluation v i hi r
    simp [φ, s2e_standardProjectiveChartEvaluation]

/-- Dehomogenization followed by chart evaluation is normalized vector evaluation.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_projective_chart_evaluation_polynomial {n : ℕ} (v : CoordinateSpace n)
    (i : Fin (n + 1)) (hi : v i ≠ 0) :
    (s2e_standardProjectiveChartEvaluation v i hi).toRingHom.comp (a3m_Pnθ n i) =
      eval (fun j => v j / v i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp [a3m_Pnθ, s2e_standardProjectiveChartEvaluation]
  · intro j
    simp only [RingHom.comp_apply, a3m_Pnθ, coe_eval₂Hom, eval₂_X, eval_X]
    change s2e_standardProjectiveChartEvaluation v i hi
      ((1 : ℂ) ⊗ₜ[ℤ] chartCoordinate i j) = _
    simp only [s2e_standardProjectiveChartEvaluation, AlgHom.liftEquiv_tmul, one_smul]
    exact s2e_projective_chartCoordinate_eval v i j hi

end HodgeLean.Foundations.QuotientDuality
