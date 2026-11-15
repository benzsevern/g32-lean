import HodgeLean.Foundations.Program.FuchsianSystemLocalForm

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65f_circle_norm (a : ℂ) (ρ t : ℝ) : ‖b65f_circle a ρ t - a‖ = |ρ| := by
  simp [b65f_circle, norm_mul, Complex.norm_exp, Complex.mul_re, Complex.mul_im]

theorem b65f_circle_hasDerivAt (a : ℂ) (ρ t : ℝ) :
    HasDerivAt (b65f_circle a ρ)
      (2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) t := by
  let c : ℂ := 2 * Real.pi * Complex.I
  have hh := (((Complex.hasDerivAt_exp (c * (t : ℂ))).scomp t
    (Complex.ofRealCLM.hasDerivAt.const_mul c)).const_mul (ρ : ℂ)).const_add a
  convert hh using 1
  · funext s
    rfl
  · simp only [b65f_circle, add_sub_cancel_left, Complex.ofRealCLM_apply, Complex.ofReal_one]
    dsimp [c]
    ring

theorem b65f_circle_one_eq_zero (a : ℂ) (ρ : ℝ) :
    b65f_circle a ρ 1 = b65f_circle a ρ 0 := by
  simp [b65f_circle, Complex.exp_two_pi_mul_I]

theorem b65f_lifted_circle_endpoint {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] (R : E →L[ℂ] E) (H : ℂ → E →L[ℂ] E) (a : ℂ) (ρ : ℝ) :
    let Q := fun t : ℝ ↦ H (b65f_circle a ρ t) *
      NormedSpace.exp ((Complex.log (ρ : ℂ) + 2 * Real.pi * Complex.I * (t : ℂ)) • R)
    Q 1 = Q 0 * NormedSpace.exp ((2 * Real.pi * Complex.I) • R) := by
  let : NormedAlgebra ℚ (E →L[ℂ] E) := NormedAlgebra.restrictScalars ℚ ℂ (E →L[ℂ] E)
  dsimp only
  rw [b65f_circle_one_eq_zero]
  simp only [Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero, add_zero]
  rw [add_smul, NormedSpace.exp_add_of_commute
    (((Commute.refl R).smul_left (Complex.log (ρ : ℂ))).smul_right (2 * Real.pi * Complex.I))]
  simp only [mul_assoc]

theorem b65f_lifted_circle_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (R : E →L[ℂ] E) (B H : ℂ → E →L[ℂ] E) (a : ℂ) (ρ t : ℝ)
    (hρ : 0 < ρ) (hH : DifferentiableAt ℂ H (b65f_circle a ρ t))
    (hg : (b65f_circle a ρ t - a) • deriv H (b65f_circle a ρ t) =
      R * H (b65f_circle a ρ t) - H (b65f_circle a ρ t) * R +
        (b65f_circle a ρ t - a) • (B (b65f_circle a ρ t) * H (b65f_circle a ρ t))) :
    let Q := fun s : ℝ ↦ H (b65f_circle a ρ s) *
      NormedSpace.exp ((Complex.log (ρ : ℂ) + 2 * Real.pi * Complex.I * (s : ℂ)) • R)
    HasDerivAt Q ((2 * Real.pi * Complex.I * (b65f_circle a ρ t - a)) •
      (((b65f_circle a ρ t - a)⁻¹ • R + B (b65f_circle a ρ t)) * Q t)) t := by
  let c : ℂ := 2 * Real.pi * Complex.I
  have hw : b65f_circle a ρ t - a ≠ 0 := by
    apply norm_pos_iff.mp
    rw [b65f_circle_norm, abs_of_pos hρ]
    exact hρ
  have he := (hasDerivAt_exp_smul_const' R (Complex.log (ρ : ℂ) + c * (t : ℂ))).scomp t
    ((Complex.ofRealCLM.hasDerivAt.const_mul c).const_add (Complex.log (ρ : ℂ)))
  have hh := (hH.hasDerivAt.scomp t (b65f_circle_hasDerivAt a ρ t)).mul he
  dsimp only
  convert hh using 1
  · funext s
    rfl
  · simp only [Function.comp_apply, Complex.ofRealCLM_apply, Complex.ofReal_one, mul_one]
    rw [b65f_gauge_derivative_rescale R B H a (b65f_circle a ρ t) hw hg]
    dsimp only [c]
    simp only [add_mul, smul_add, smul_sub, sub_mul, smul_mul_assoc, mul_smul_comm,
      smul_smul, mul_assoc, mul_inv_cancel₀ hw, mul_one]
    abel

end HodgeLean.Foundations.Program
