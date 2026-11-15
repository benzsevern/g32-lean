import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationCone
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Evaluation of the actual projective tensor charts -/

noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluate the actual complex tensor chart at a normalized homogeneous vector.
Source: Algebra.TensorProduct.lift; ComplexProjectiveSpace.awayCoordinateEvaluation.
-/
def retainedProjectiveChartEvaluation {N : ℕ} (v : CoordinateSpace N)
    (j : Fin (N+1)) (hj : v j ≠ 0) : a3m_PnT N j →+* ℂ :=
  (Algebra.TensorProduct.lift (RingHom.id ℂ).toIntAlgHom
    (awayCoordinateEvaluation v j hj).toIntAlgHom (fun _ _ => Commute.all _ _)).toRingHom

/-- Evaluation on the actual tensor chart factors the original vector-to-projective morphism. -/
lemma retained_projective_vector_chart_factorization {N : ℕ} (v : CoordinateSpace N)
    (hv : v ≠ 0) (j : Fin (N+1)) (hj : v j ≠ 0) :
    Spec.map (CommRingCat.ofHom (retainedProjectiveChartEvaluation v j hj)) ≫ a3m_Pnκ N j =
      vectorToProjectiveSpace v hv := by
  have hb : vectorToProjectiveSpace v hv ≫
      pullback.fst (terminal.from (Spec ↧ℂ)) (terminal.from (HodgeLean.Foundations.g3c_P N)) = 𝟙 _ :=
    vectorToProjectiveSpace_toBase v hv
  have hs : vectorToProjectiveSpace v hv ≫
      pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (HodgeLean.Foundations.g3c_P N)) =
        chartIntegralProjAt v j hj :=
    (vectorToProjectiveSpace_toProj v hv).trans (chartIntegralProj_eq_chartIntegralProjAt v hv j hj)
  apply pullback.hom_ext
  · rw [Category.assoc, a3m_Pnκ, a3m_prodChart_fst, Category.comp_id, ← Spec.map_comp,
      hb]
    change Spec.map (CommRingCat.ofHom ((retainedProjectiveChartEvaluation v j hj).comp
      (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ)
        (B := HomogeneousLocalization.Away (UniversalGrading N) (MvPolynomial.X j))))) = 𝟙 _
    have he : (retainedProjectiveChartEvaluation v j hj).comp
        (Algebra.TensorProduct.includeLeftRingHom (R := ℤ) (A := ℂ)
          (B := HomogeneousLocalization.Away (UniversalGrading N) (MvPolynomial.X j))) = RingHom.id ℂ := by
      ext x
      simp [retainedProjectiveChartEvaluation]
    rw [he]
    exact Spec.map_id _
  · rw [Category.assoc, a3m_Pnκ, a3m_prodChart_snd, ← Category.assoc, ← Spec.map_comp,
      hs]
    change Spec.map (CommRingCat.ofHom ((retainedProjectiveChartEvaluation v j hj).comp
      (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ)).toRingHom)) ≫ _ = _
    have he : (retainedProjectiveChartEvaluation v j hj).comp
        (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℂ)).toRingHom =
          awayCoordinateEvaluation v j hj := by
      ext x
      simp [retainedProjectiveChartEvaluation]
    rw [he]
    rfl

/-- The original tensor-chart polynomial evaluation is evaluation at the normalized homogeneous coordinates. -/
lemma retained_projective_chart_polynomial_evaluation {N : ℕ} (v : CoordinateSpace N)
    (j : Fin (N+1)) (hj : v j ≠ 0) (F : MvPolynomial (Fin (N+1)) ℂ) :
    retainedProjectiveChartEvaluation v j hj (a3m_Pnθ N j F) =
      MvPolynomial.eval (fun k => v k / v j) F := by
  have he : (retainedProjectiveChartEvaluation v j hj).comp (a3m_Pnθ N j) =
      MvPolynomial.eval (fun k => v k / v j) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [retainedProjectiveChartEvaluation, a3m_Pnθ]
    · intro k
      simp [retainedProjectiveChartEvaluation, a3m_Pnθ, s2e_projective_chartCoordinate_eval]
  exact DFunLike.congr_fun he F

end HodgeLean.Foundations.QuotientDuality
