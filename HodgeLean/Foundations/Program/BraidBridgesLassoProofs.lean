import HodgeLean.Foundations.Program.BraidBridgesDefs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b65x_exp_arctan (t : ℝ) :
    Complex.exp (((2 * Real.arctan t : ℝ) : ℂ) * Complex.I) = b65x_et t := by
  have hp : 0 < 1 + t ^ 2 := by positivity
  have ht : Real.sin (Real.arctan t) = t * Real.cos (Real.arctan t) := by
    have h := Real.tan_arctan t
    rw [Real.tan_eq_sin_div_cos, div_eq_iff (ne_of_gt (Real.cos_arctan_pos t))] at h
    exact h
  apply Complex.ext
  · simp only [Complex.exp_re, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
      mul_one, zero_add, add_zero, Real.exp_zero, one_mul, b65x_et, Complex.div_ofReal_re,
      Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.one_re]
    rw [Real.cos_two_mul, Real.cos_sq_arctan]
    field_simp
    <;> ring
  · simp only [Complex.exp_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, zero_mul,
      mul_one, zero_add, add_zero, Real.exp_zero, one_mul, b65x_et, Complex.div_ofReal_im,
      Complex.add_im]
    rw [Real.sin_two_mul, ht]
    calc
      2 * (t * Real.cos (Real.arctan t)) * Real.cos (Real.arctan t) =
          2 * t * Real.cos (Real.arctan t) ^ 2 := by ring
      _ = _ := by rw [Real.cos_sq_arctan]; ring

theorem b65x_exp_quarters (t : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((1/4 + Real.arctan t / Real.pi : ℝ) : ℂ)) =
        Complex.I * b65x_et t ∧
    Complex.exp (2 * Real.pi * Complex.I * ((3/4 + Real.arctan t / Real.pi : ℝ) : ℂ)) =
        -Complex.I * b65x_et t ∧
    Complex.exp (-(2 * Real.pi * Complex.I * ((1/4 - Real.arctan t / Real.pi : ℝ) : ℂ))) =
        -Complex.I * b65x_et t ∧
    Complex.exp (-(2 * Real.pi * Complex.I * ((3/4 - Real.arctan t / Real.pi : ℝ) : ℂ))) =
        Complex.I * b65x_et t := by
  have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have h1 : 2 * Real.pi * Complex.I * ((1/4 + Real.arctan t / Real.pi : ℝ) : ℂ) =
      (Real.pi : ℂ) / 2 * Complex.I + ((2 * Real.arctan t : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [hpi]
    <;> ring
  have h3 : 2 * Real.pi * Complex.I * ((3/4 + Real.arctan t / Real.pi : ℝ) : ℂ) =
      (Real.pi : ℂ) * Complex.I +
        ((Real.pi : ℂ) / 2 * Complex.I + ((2 * Real.arctan t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp [hpi]
    <;> ring
  have hn1 : -(2 * Real.pi * Complex.I * ((1/4 - Real.arctan t / Real.pi : ℝ) : ℂ)) =
      -((Real.pi : ℂ) / 2 * Complex.I) + ((2 * Real.arctan t : ℝ) : ℂ) * Complex.I := by
    push_cast
    field_simp [hpi]
    <;> ring
  have hn3 : -(2 * Real.pi * Complex.I * ((3/4 - Real.arctan t / Real.pi : ℝ) : ℂ)) =
      -((Real.pi : ℂ) * Complex.I) +
        (-((Real.pi : ℂ) / 2 * Complex.I) + ((2 * Real.arctan t : ℝ) : ℂ) * Complex.I) := by
    push_cast
    field_simp [hpi]
    <;> ring
  rw [h1, h3, hn1, hn3]
  simp only [Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I,
    Complex.exp_pi_div_two_mul_I, b65x_exp_arctan, inv_neg, inv_one, Complex.inv_I]
  constructor
  · trivial
  constructor
  · ring
  constructor
  · trivial
  · ring

theorem b65x_lasso_circle (i : Fin 13) (hi : i ≠ 0) (s : ℝ)
    (hs0 : 1/3 ≤ s) (hs1 : s ≤ 2/3) :
    b65b_lasso i s = b65x_centre i + Complex.I * (b65x_radius i : ℂ) *
      Complex.exp (2 * Real.pi * Complex.I * (3 * s - 1 : ℂ)) := by
  have hi0 : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
  simp only [b65b_lasso, b65x_centre, b65x_radius, hi0, dite_false]
  by_cases h : s ≤ 1/3
  · rw [ite_eq_left h]
    have he : s = 1/3 := by linarith
    subst s
    norm_num
  · rw [ite_eq_right h, ite_eq_left hs1]
    simp only [Complex.ofReal_ratCast]

theorem b65x_arctan_ratio_bounds (t : ℝ) (ht : t ∈ Set.Icc (-1 : ℝ) 1) :
    -(1/4 : ℝ) ≤ Real.arctan t / Real.pi ∧ Real.arctan t / Real.pi ≤ 1/4 := by
  have hl := Real.arctan_mono ht.1
  have hr := Real.arctan_mono ht.2
  rw [Real.arctan_neg, Real.arctan_one] at hl
  rw [Real.arctan_one] at hr
  constructor
  · apply (le_div_iff₀ Real.pi_pos).mpr
    linarith
  · apply (div_le_iff₀ Real.pi_pos).mpr
    linarith

theorem b65x_lasso_segments (i : Fin 13) (hi : i ≠ 0) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    b65b_lasso i (t / 3) = b65x_piece i 0 t ∧
      b65b_lasso i (1 - t / 3) = b65x_piece i 0 t := by
  have hi0 : i.val ≠ 0 := by intro h; exact hi (Fin.ext h)
  constructor
  · have h : t / 3 ≤ 1/3 := by linarith [ht.2]
    simp only [b65b_lasso, hi0, dite_false, ite_eq_left h, b65x_piece,
      Matrix.cons_val_zero, b65x_centre, b65x_radius]
    push_cast
    ring
  · by_cases ht1 : t = 1
    · subst t
      norm_num [b65b_lasso, b65x_piece, b65x_centre, b65x_radius, hi0,
        Complex.exp_two_pi_mul_I]
      <;> ring
    · have h0 : ¬ 1 - t / 3 ≤ 1/3 := by linarith [ht.2]
      have h1 : ¬ 1 - t / 3 ≤ 2/3 := by
        have : t < 1 := lt_of_le_of_ne ht.2 ht1
        linarith
      simp only [b65b_lasso, hi0, dite_false, ite_eq_right h0, ite_eq_right h1, b65x_piece,
        Matrix.cons_val_zero, b65x_centre, b65x_radius]
      push_cast
      ring

end HodgeLean.Foundations.Program
