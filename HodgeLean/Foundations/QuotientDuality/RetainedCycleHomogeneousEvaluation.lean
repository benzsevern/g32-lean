import HodgeLean.Foundations.QuotientDuality.RetainedCycleProjectiveChartValues

/-! Homogeneous evaluation under scalar normalization. -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Evaluating a homogeneous polynomial on scaled coordinates scales by its degree.
Source: Hartshorne, Algebraic Geometry, I.2. -/
lemma retained_homogeneous_eval_scale {ι : Type} (v : ι → ℂ) (a : ℂ)
    (p : MvPolynomial ι ℂ) (d : ℕ) (hp : p.IsHomogeneous d) :
    eval (fun i => a * v i) p = a ^ d * eval v p := by
  classical
  simp only [eval_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    ← hp.degree_eq_sum_deg_support hs]
  ring

/-- The projection atlas prime detects vanishing at the original homogeneous vector.
Source: Hartshorne, Algebraic Geometry, I.2 and II.7. -/
lemma retained_projective_prime_evaluation {n d : ℕ} (v : CoordinateSpace n) (hv : v ≠ 0)
    (p : MvPolynomial (Fin (n+1)) ℂ) (hp : p.IsHomogeneous d) :
    p ∈ (a3m_projCharts n).prime (vectorToComplexPoint v hv).underlying ↔ eval v p = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne_zero v hv
  let φ := s2e_standardProjectiveChartEvaluation v i hi
  let x := Spec.map (CommRingCat.ofHom φ.toRingHom) (IsLocalRing.closedPoint ℂ)
  have hx : a3m_Pnκ n i x = (vectorToComplexPoint v hv).underlying :=
    congrArg (fun f => f (IsLocalRing.closedPoint ℂ))
      (retained_projective_chart_evaluation_point v i hi)
  rw [(a3m_projCharts n).mem_prime_iff_of_isHomogeneous _ i x hx p d hp]
  change φ (a3m_Pnθ n i p) ∈ (IsLocalRing.closedPoint ℂ).asIdeal ↔ _
  change ((φ.toRingHom.comp (a3m_Pnθ n i)) p) ∈ (IsLocalRing.closedPoint ℂ).asIdeal ↔ _
  rw [retained_projective_chart_evaluation_polynomial]
  have he : (fun j => v j / v i) = (fun j => (v i)⁻¹ * v j) := by
    funext j
    exact div_eq_inv_mul _ _
  rw [he, retained_homogeneous_eval_scale _ _ p d hp]
  simp [IsLocalRing.closedPoint, IsLocalRing.maximalIdeal_eq_bot, hi]

end HodgeLean.Foundations.QuotientDuality
