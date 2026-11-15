import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000

theorem symplectic_quadratic_imaginary {g : ℕ} (T : Fin g → Fin g → ℂ)
    (hT : ∀ i j, T i j = T j i) (z : Fin g → ℂ) :
    (Complex.I * ∑ j,
      ((-∑ i, z i * T i j) * star (z j) - z j * star (-∑ i, z i * T i j))).re =
      2 * (∑ i, ∑ j, star (z i) * T i j * z j).im := by
  let a : Fin g → ℂ := fun j => -∑ i, z i * T i j
  let S := ∑ i, ∑ j, star (z i) * T i j * z j
  have hs : (∑ j, star (z j) * a j) = -S := by
    dsimp [a, S]
    simp only [mul_neg, Finset.mul_sum, Finset.sum_neg_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hT j i]
    ring
  have hp : (∑ j, (a j * star (z j) - z j * star (a j))) =
      (∑ j, star (z j) * a j) - star (∑ j, star (z j) * a j) := by
    rw [star_sum, Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro j hj
      ring
    · apply Finset.sum_congr rfl
      intro j hj
      simp only [star_mul, star_star] <;> ring
  change (Complex.I * ∑ j, (a j * star (z j) - z j * star (a j))).re = 2 * S.im
  rw [hp, hs]
  simp only [star_neg, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.sub_im,
    Complex.neg_im, Complex.star_def, Complex.conj_im, zero_mul, zero_sub]
  ring

end HodgeLean.Foundations.Curves.AbelTheorem
