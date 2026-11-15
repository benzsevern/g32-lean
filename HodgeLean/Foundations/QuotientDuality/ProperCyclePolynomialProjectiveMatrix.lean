import HodgeLean.Foundations.QuotientDuality.ProperCycleMatrixRealCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrix

/-! # Actual rational matrix coordinates of polynomial homogeneous vectors -/

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The original squared complex mass is a real polynomial in specified polynomial vector coordinates.
Source: Complex.normSq_apply; properCycle_projective_matrix_mass.
HC no distance; AV milestone no distance. -/
def properCycle_polynomial_vector_mass {n : ℕ} {ι : Type} [Fintype ι]
    (a b : ι → MvPolynomial (Fin n) ℝ) : MvPolynomial (Fin n) ℝ :=
  ∑ i, (a i * a i + b i * b i)

/-- The real polynomial mass evaluates to the original squared complex vector mass.
Source: Complex.normSq_apply; MvPolynomial.eval_sum.
HC no distance; AV milestone no distance. -/
theorem properCycle_polynomial_vector_mass_eval {n : ℕ} {ι : Type} [Fintype ι]
    (a b : ι → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n)) :
    MvPolynomial.eval x (properCycle_polynomial_vector_mass a b) =
      properCycle_projective_matrix_mass (fun i =>
        (⟨MvPolynomial.eval x (a i), MvPolynomial.eval x (b i)⟩ : ℂ)) := by
  simp [properCycle_polynomial_vector_mass, properCycle_projective_matrix_mass,
    Complex.normSq_apply]

/-- Real numerators of the original normalized outer product retain the literal matrix entry order.
Source: Complex.mul_re; Complex.mul_im; properCycle_projective_matrix.
HC no distance; AV milestone no distance. -/
def properCycle_polynomial_matrix_numerator {n : ℕ} {ι : Type} [Fintype ι]
    (a b : ι → MvPolynomial (Fin n) ℝ) :
    Fin (Fintype.card ((ι × ι) ⊕ (ι × ι))) → MvPolynomial (Fin n) ℝ :=
  fun k => Sum.elim
    (fun ij => a ij.1 * a ij.2 + b ij.1 * b ij.2)
    (fun ij => b ij.1 * a ij.2 - a ij.1 * b ij.2)
    ((Fintype.equivFin ((ι × ι) ⊕ (ι × ι))).symm k)

/-- The actual normalized complex matrix map has the specified real polynomial numerators and its original squared mass denominator.
Source: Complex.div_ofReal_re; Complex.div_ofReal_im; properCycle_matrix_euclidean_coordinates_eval.
HC no distance; AV milestone no distance. -/
theorem properCycle_polynomial_matrix_rational_eval {n : ℕ} {ι : Type} [Fintype ι]
    (a b : ι → MvPolynomial (Fin n) ℝ) (x : EuclideanSpace ℝ (Fin n))
    (k : Fin (Fintype.card ((ι × ι) ⊕ (ι × ι)))) :
    properCycle_matrix_euclidean_coordinates (properCycle_projective_matrix (fun i =>
      (⟨MvPolynomial.eval x (a i), MvPolynomial.eval x (b i)⟩ : ℂ))) k =
      MvPolynomial.eval x (properCycle_polynomial_matrix_numerator a b k) /
        MvPolynomial.eval x (properCycle_polynomial_vector_mass a b) := by
  let v : ι → ℂ := fun i => ⟨MvPolynomial.eval x (a i), MvPolynomial.eval x (b i)⟩
  have hk := properCycle_matrix_euclidean_coordinates_eval (properCycle_projective_matrix v)
    ((Fintype.equivFin ((ι × ι) ⊕ (ι × ι))).symm k)
  simp only [Equiv.apply_symm_apply] at hk
  rw [hk, properCycle_polynomial_vector_mass_eval]
  unfold properCycle_polynomial_matrix_numerator
  generalize (Fintype.equivFin ((ι × ι) ⊕ (ι × ι))).symm k = t
  cases t with
  | inl ij =>
    change (v ij.1 * star (v ij.2) / (properCycle_projective_matrix_mass v : ℂ)).re = _
    simp [Complex.mul_re, Complex.star_def, v]
  | inr ij =>
    change (v ij.1 * star (v ij.2) / (properCycle_projective_matrix_mass v : ℂ)).im = _
    simp [Complex.mul_im, Complex.star_def, v]
    ring

end HodgeLean.Foundations.QuotientDuality
