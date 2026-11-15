import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectionCentre
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectiveProjection
import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectiveLinearPrime

/-! # The literal analytic domain of the algebraic projection centre -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual common zero locus of the linear projection forms.
Source: retained_projection_forms_zero_isClosed.
-/
def retainedProjectionCentre {N n : ℕ} (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ) :
    Closeds (a3m_Pn N) :=
  ⟨{x | ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈ (a3m_projCharts N).prime x},
    retained_projection_forms_zero_isClosed ℓ⟩

/-- The original linear forms as a continuous linear map on homogeneous vectors.
Source: Matrix.mulVecLin; LinearMap.toContinuousLinearMap.
-/
def retainedProjectionLinearMap {N n : ℕ} (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ) :
    CoordinateSpace N →L[ℂ] CoordinateSpace n :=
  LinearMap.toContinuousLinearMap ℓ.mulVecLin

/-- Avoiding the actual algebraic centre is exactly the domain of the literal continuous projective projection. -/
lemma retained_projection_centre_complement_domain {N n : ℕ}
    (ℓ : Matrix (Fin (n+1)) (Fin (N+1)) ℂ) (p : Projectivization ℂ (CoordinateSpace N)) :
    (projectivizationToComplexPoint p).underlying ∉ retainedProjectionCentre ℓ ↔
      p ∈ retained_projective_projection_domain (retainedProjectionLinearMap ℓ) := by
  induction p using Projectivization.ind with
  | h v hv =>
    rw [retained_projective_projection_domain_mk]
    change (¬ ∀ i, a3r_lin ℓ (MvPolynomial.X i) ∈
      (a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying) ↔ ℓ.mulVec v ≠ 0
    have he (i : Fin (n+1)) : a3r_lin ℓ (MvPolynomial.X i) ∈
        (a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying ↔
          (ℓ.mulVec v) i = 0 := by
      rw [retained_projective_prime_mem_of_homogeneous _ _ _ 1 (a3r_lin_X_isHomogeneous ℓ i)]
      simp [a3r_lin_X, Matrix.mulVec, dotProduct]
    simp_rw [he]
    constructor
    · intro h hz
      apply h
      intro i
      rw [hz]
      rfl
    · intro h hz
      exact h (funext hz)

end HodgeLean.Foundations.QuotientDuality
