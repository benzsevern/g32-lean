import HodgeLean.Foundations.QuotientDuality.RetainedCycleHomogeneousEvaluation

/-! Homogeneous coordinate values of the specified finite projection. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluation of the actual linear forms is matrix multiplication on homogeneous coordinates.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_projection_substitution_eval {n m : ℕ}
    (ℓ : Matrix (Fin (m+1)) (Fin (n+1)) ℂ) (v : CoordinateSpace n) :
    (eval v).comp (a3r_lin ℓ).toRingHom = eval (ℓ.mulVec v) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    simp
  · intro i
    simp [a3r_lin_X, Matrix.mulVec, dotProduct]

/-- The inherited presentation prime is evaluated in its original ambient coordinates.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_presentation_prime_at_vector
    (X : Over (Spec ↧ℂ)) (D : ProjectiveSpace.Presentation X.hom)
    (x : X.left) (v : CoordinateSpace D.ambientDimension) (hv : v ≠ 0)
    (hx : D.immersion x = (vectorToComplexPoint v hv).underlying)
    {d : ℕ} (p : MvPolynomial (Fin (D.ambientDimension+1)) ℂ) (hp : p.IsHomogeneous d) :
    p ∈ (retained_presentation_charts X D).prime x ↔ eval v p = 0 := by
  letI : IsClosedImmersion D.immersion := D.isClosedImmersion
  change p ∈ ((a3m_projCharts D.ambientDimension).restrict D.immersion).prime x ↔ _
  rw [a3m_SpecCharts.restrict_prime]
  erw [hx]
  exact retained_projective_prime_evaluation v hv p hp

/-- A point in the inherited presentation avoids the matrix kernel of finite parameters.
Source: Hartshorne, Algebraic Geometry, II.7. -/
lemma retained_presentation_vector_not_kernel
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (D : ProjectiveSpace.Presentation X.hom) {m : ℕ}
    (ℓ : Matrix (Fin (m+1)) (Fin (D.ambientDimension+1)) ℂ)
    (hfin : ((Ideal.Quotient.mk (retained_presentation_cone_ideal X D)).comp
      (a3r_lin ℓ).toRingHom).Finite)
    (x : X.left) (v : CoordinateSpace D.ambientDimension) (hv : v ≠ 0)
    (hx : D.immersion x = (vectorToComplexPoint v hv).underlying) :
    ℓ.mulVec v ≠ 0 := by
  obtain ⟨i, hi⟩ := retained_presentation_exists_notMem X D ℓ hfin x
  rw [retained_presentation_prime_at_vector X D x v hv hx _
    (a3r_lin_X_isHomogeneous ℓ i)] at hi
  change ((eval v).comp (a3r_lin ℓ).toRingHom) (MvPolynomial.X i) ≠ 0 at hi
  rw [retained_projection_substitution_eval, eval_X] at hi
  intro h
  exact hi (congrFun h i)

end HodgeLean.Foundations.QuotientDuality
