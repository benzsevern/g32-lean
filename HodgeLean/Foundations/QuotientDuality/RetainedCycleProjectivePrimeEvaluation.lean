import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectiveEvaluation

/-! # Homogeneous prime membership of the actual complex projective point -/

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace MvPolynomial
open HodgeLean.Adapters HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.QuotientDuality

/-- A homogeneous complex polynomial belongs to the actual projective point prime precisely when it evaluates to zero. -/
lemma retained_projective_prime_mem_of_homogeneous {N : ℕ} (v : CoordinateSpace N)
    (hv : v ≠ 0) (F : MvPolynomial (Fin (N+1)) ℂ) (d : ℕ) (hF : F.IsHomogeneous d) :
    F ∈ (a3m_projCharts N).prime (vectorToComplexPoint v hv).underlying ↔
      MvPolynomial.eval v F = 0 := by
  classical
  obtain ⟨j, hj⟩ := exists_coordinate_ne_zero v hv
  let φ := retainedProjectiveChartEvaluation v j hj
  let p : Spec (a3m_PnT N j) := Spec.map (CommRingCat.ofHom φ) (IsLocalRing.closedPoint ℂ)
  have hp : (a3m_projCharts N).κ j p = (vectorToComplexPoint v hv).underlying :=
    congrArg (fun f => f (IsLocalRing.closedPoint ℂ))
      (retained_projective_vector_chart_factorization v hv j hj)
  rw [(a3m_projCharts N).mem_prime_iff_of_isHomogeneous _ j p hp F d hF]
  change φ (a3m_Pnθ N j F) ∈ IsLocalRing.maximalIdeal ℂ ↔ _
  rw [IsLocalRing.maximalIdeal_eq_bot]
  change φ (a3m_Pnθ N j F) = 0 ↔ _
  rw [retained_projective_chart_polynomial_evaluation]
  have hs := a3m_twist (MvPolynomial.eval (fun k => v k / v j)) (MvPolynomial.eval v)
    (v j)⁻¹ (fun c => by simp) (fun k => by simp [div_eq_mul_inv, mul_comm]) F d hF
  rw [hs]
  exact mul_eq_zero_iff_left (pow_ne_zero d (inv_ne_zero hj))

end HodgeLean.Foundations.QuotientDuality
