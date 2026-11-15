import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrix

/-! # Literal finite equations of normalized projective matrices -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual normalized outer-product coordinates form a Hermitian matrix.
Source: Mathlib, star_div, star_mul and Complex.conj_ofReal.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_conjugate {ι : Type} [Fintype ι]
    (v : ι → ℂ) (i j : ι) :
    star (properCycle_projective_matrix v i j) = properCycle_projective_matrix v j i := by
  simp only [properCycle_projective_matrix, Matrix.of_apply, Complex.star_def, map_div₀, map_mul,
    starRingEnd_self_apply, Complex.conj_ofReal]
  ring

/-- Every original two-by-two minor of the actual normalized projective matrix vanishes.
Source: Mathlib, commutative field arithmetic; the normalized outer-product formula.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_minor {ι : Type} [Fintype ι]
    (v : ι → ℂ) (i j k l : ι) :
    properCycle_projective_matrix v i j * properCycle_projective_matrix v k l =
      properCycle_projective_matrix v i l * properCycle_projective_matrix v k j := by
  simp only [properCycle_projective_matrix, Matrix.of_apply]
  ring

/-- The actual normalized matrix has nonnegative real diagonal coordinates.
Source: Mathlib, Complex.mul_conj, Complex.div_ofReal_re and Complex.normSq_nonneg.
HC no distance; AV milestone no distance. -/
lemma properCycle_projective_matrix_diagonal_nonnegative {ι : Type} [Fintype ι]
    (v : ι → ℂ) (i : ι) : 0 ≤ (properCycle_projective_matrix v i i).re := by
  have hm : 0 ≤ properCycle_projective_matrix_mass v :=
    Finset.sum_nonneg fun j _ => Complex.normSq_nonneg (v j)
  change 0 ≤ (v i * star (v i) / (properCycle_projective_matrix_mass v : ℂ)).re
  rw [show v i * star (v i) = (Complex.normSq (v i) : ℂ) from Complex.mul_conj (v i),
    Complex.div_ofReal_re, Complex.ofReal_re]
  exact div_nonneg (Complex.normSq_nonneg (v i)) hm

end HodgeLean.Foundations.QuotientDuality
