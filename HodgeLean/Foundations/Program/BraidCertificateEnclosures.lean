import HodgeLean.Foundations.Program.BraidCertificateDefs

namespace HodgeLean.Foundations.Program

theorem b65b_normalization_denominator (k : Fin 12) (z : ℂ) (a b : ℝ)
    (hz : |z.re - ((b65b_boxCentre k).1 : ℝ)| ≤ (1/10000 : ℝ))
    (ha : |a - ((b65b_boxCentre 0).1 : ℝ)| ≤ (1/10000 : ℝ))
    (hb : |b - ((b65b_boxCentre 6).1 : ℝ)| ≤ (1/10000 : ℝ)) :
    z * ((b : ℂ) - a) ≠ 0 := by
  apply mul_ne_zero
  · intro he
    rw [he] at hz
    fin_cases k <;> norm_num [b65b_boxCentre] at hz
  · intro he
    have hr := congrArg Complex.re he
    norm_num at hr
    have ha' := abs_le.mp ha
    have hb' := abs_le.mp hb
    norm_num [b65b_boxCentre] at ha' hb'
    linarith

theorem b65b_square_endpoint_bound (x c lo hi : ℝ) (hx : x ∈ Set.Icc lo hi) :
    (x - c)^2 ≤ (lo - c)^2 ∨ (x - c)^2 ≤ (hi - c)^2 := by
  by_cases hc : x ≤ c
  · left
    have h := mul_nonneg (sub_nonneg.mpr hx.1)
      (show 0 ≤ 2*c-x-lo by linarith [hx.1])
    nlinarith
  · right
    have h := mul_nonneg (sub_nonneg.mpr hx.2)
      (show 0 ≤ hi+x-2*c by linarith [hx.2])
    nlinarith

theorem b65b_rectangle_bound (z : ℂ) (cx cy r lo hi bot top : ℝ)
    (hr : 0 < r) (hx : z.re ∈ Set.Icc lo hi) (hy : z.im ∈ Set.Icc bot top)
    (h00 : (lo-cx)^2 + (bot-cy)^2 < r^2)
    (h01 : (lo-cx)^2 + (top-cy)^2 < r^2)
    (h10 : (hi-cx)^2 + (bot-cy)^2 < r^2)
    (h11 : (hi-cx)^2 + (top-cy)^2 < r^2) :
    ‖z - (cx + cy * Complex.I)‖ < r := by
  have hs : ‖z - (cx + cy * Complex.I)‖ ^ 2 < r^2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      mul_zero, zero_mul, sub_zero, add_zero, Complex.sub_im, Complex.add_im,
      Complex.mul_im, zero_add, mul_one]
    rcases b65b_square_endpoint_bound z.re cx lo hi hx with hx' | hx' <;>
      rcases b65b_square_endpoint_bound z.im cy bot top hy with hy' | hy' <;>
      nlinarith
  nlinarith [norm_nonneg (z - (cx + cy * Complex.I))]

end HodgeLean.Foundations.Program
