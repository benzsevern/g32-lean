import HodgeLean.Foundations.Program.G32Native.PELRealCayleyComponent

noncomputable section
namespace HodgeLean.Foundations
variable {n : ℕ}

/-- The real linear skew-centralizer of a bilinear form and retained operators. -/
def pel_real_skew_centralizer (E : Matrix (Fin n) (Fin n) ℝ)
    (S : Set (Matrix (Fin n) (Fin n) ℝ)) :
    Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {X | X.transpose * E + E * X = 0 ∧ ∀ T ∈ S, X * T = T * X}
  zero_mem' := by simp
  add_mem' := by
    rintro X Y ⟨hX, hXC⟩ ⟨hY, hYC⟩
    constructor
    · rw [Matrix.transpose_add, add_mul, mul_add, add_add_add_comm, hX, hY, zero_add]
    · intro T hT
      rw [add_mul, mul_add, hXC T hT, hYC T hT]
  smul_mem' := by
    rintro r X ⟨hX, hXC⟩
    constructor
    · rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hX, smul_zero]
    · intro T hT
      rw [Matrix.smul_mul, Matrix.mul_smul, hXC T hT]

/-- Real and imaginary parts preserve the bilinear skew equation of a real form. -/
theorem pel_real_imag_bilinear_skew
    (E : Matrix (Fin n) (Fin n) ℝ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y.transpose * E.map Complex.ofReal + E.map Complex.ofReal * Y = 0) :
    (Y.map Complex.re).transpose * E + E * Y.map Complex.re = 0 ∧
    (Y.map Complex.im).transpose * E + E * Y.map Complex.im = 0 := by
  constructor
  · ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).re) hY
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Complex.add_re, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero,
      Matrix.zero_apply, Complex.zero_re] using h
  · ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).im) hY
    simpa only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply,
      Matrix.map_apply, Complex.add_im, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add,
      Matrix.zero_apply, Complex.zero_im] using h

/-- Commutation with a real matrix passes to real and imaginary parts. -/
theorem pel_real_imag_commute
    (T : Matrix (Fin n) (Fin n) ℝ) (Y : Matrix (Fin n) (Fin n) ℂ)
    (hY : Y * T.map Complex.ofReal = T.map Complex.ofReal * Y) :
    Y.map Complex.re * T = T * Y.map Complex.re ∧
    Y.map Complex.im * T = T * Y.map Complex.im := by
  constructor
  · ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).re) hY
    simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.re_sum, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, sub_zero] using h
  · ext i j
    have h := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => (M i j).im) hY
    simpa only [Matrix.mul_apply, Matrix.map_apply, Complex.im_sum, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add] using h

end HodgeLean.Foundations
