import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectivePrimeEvaluation
import HodgeLean.Foundations.QuotientDuality.RetainedCyclePresentationProjection

/-! # Homogeneous primes under the literal projective linear projection -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
open HodgeLean.Adapters
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal projected homogeneous vector has the pullback prime of the actual source vector. -/
lemma retained_projective_linear_prime {N n : ℕ}
    (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ)
    (v : CoordinateSpace N) (hv : v ≠ 0) (hw : ℓ.mulVec v ≠ 0) :
    (a3m_projCharts n).prime (vectorToComplexPoint (ℓ.mulVec v) hw).underlying =
      ((a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying).comap (a3r_lin ℓ) := by
  have he : (MvPolynomial.eval v).comp (a3r_lin ℓ).toRingHom =
      MvPolynomial.eval (ℓ.mulVec v) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [a3r_lin_C]
    · intro i
      simp [a3r_lin_X, Matrix.mulVec, dotProduct]
  ext F
  change F ∈ (a3m_projCharts n).prime (vectorToComplexPoint (ℓ.mulVec v) hw).underlying ↔
    a3r_lin ℓ F ∈ (a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying
  rw [mem_iff_homogeneousComponent_mem ((a3m_projCharts n).isHomogeneous_prime _),
    mem_iff_homogeneousComponent_mem ((a3m_projCharts N).isHomogeneous_prime _)]
  apply forall_congr'
  intro d
  rw [a3h_lin_homogeneousComponent,
    retained_projective_prime_mem_of_homogeneous _ _ _ d (homogeneousComponent_isHomogeneous d F),
    retained_projective_prime_mem_of_homogeneous _ _ _ d
      (a3h_lin_isHomogeneous ℓ (homogeneousComponent_isHomogeneous d F))]
  exact iff_of_eq ((congrArg (fun f : MvPolynomial (Fin (n+1)) ℂ →+* ℂ =>
    f (homogeneousComponent d F) = 0) he).symm)

end HodgeLean.Foundations.QuotientDuality
