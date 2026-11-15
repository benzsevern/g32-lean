import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentre
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectiveProjection

/-! Coordinate description of the actual algebraic projection centre. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The algebraic centre contains a homogeneous point exactly when its vector lies in the matrix kernel.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_projection_centre_vector {N d : ℕ}
    (ℓ : Matrix (Fin (d+1)) (Fin (N+1)) ℂ) (v : CoordinateSpace N) (hv : v ≠ 0) :
    (vectorToComplexPoint v hv).underlying ∈ retained_projection_centre ℓ ↔ ℓ.mulVec v = 0 := by
  change (∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈
    (a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying) ↔ _
  have h (i : Fin (d+1)) : a3r_lin ℓ (MvPolynomial.X i) ∈
      (a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying ↔ ℓ.mulVec v i = 0 := by
    rw [retained_projective_prime_evaluation v hv _ (a3r_lin_X_isHomogeneous ℓ i)]
    change ((eval v).comp (a3r_lin ℓ).toRingHom) (MvPolynomial.X i) = 0 ↔ _
    rw [retained_projection_substitution_eval, eval_X]
  simp only [h]
  exact ⟨fun e => funext e, fun e i => congrFun e i⟩

end HodgeLean.Foundations.QuotientDuality
