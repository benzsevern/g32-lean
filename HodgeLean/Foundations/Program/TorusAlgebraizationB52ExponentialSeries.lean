import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

noncomputable section
namespace HodgeLean.Foundations.Program

theorem b52_exponential_derivative_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : E →L[ℂ] ℂ) (c : ℂ) (R : ℝ) (z : E) (hz : ‖z‖ ≤ R) :
    ‖(c * Complex.exp (A z)) • A‖ ≤ ‖c‖ * Real.exp (‖A‖ * (R + 1)) := by
  have hre : (A z).re ≤ ‖A‖ * R :=
    (Complex.re_le_norm _).trans ((A.le_opNorm z).trans
      (mul_le_mul_of_nonneg_left hz (norm_nonneg _)))
  have hA : ‖A‖ ≤ Real.exp ‖A‖ :=
    (le_add_of_nonneg_right (show (0 : ℝ) ≤ 1 by norm_num)).trans (Real.add_one_le_exp _)
  rw [norm_smul, norm_mul, Complex.norm_exp, mul_assoc]
  calc
    ‖c‖ * (Real.exp (A z).re * ‖A‖) ≤
        ‖c‖ * (Real.exp (‖A‖ * R) * Real.exp ‖A‖) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (Real.exp_le_exp.mpr hre) hA (norm_nonneg _) (Real.exp_pos _).le)
        (norm_nonneg _)
    _ = _ := by rw [← Real.exp_add]; congr 2; ring

#print axioms b52_exponential_derivative_bound

theorem b52_differentiable_exponential_series {ι E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ι → E →L[ℂ] ℂ) (c : ι → ℂ)
    (hs : ∀ R : ℝ, Summable (fun i ↦ ‖c i‖ * Real.exp (‖A i‖ * R))) :
    Differentiable ℂ (fun z ↦ ∑' i, c i * Complex.exp (A i z)) := by
  letI := NormedSpace.restrictScalars ℝ ℂ E
  have hc : Summable c := Summable.of_norm (by simpa using hs 0)
  have hf : ∀ i z, HasFDerivAt (fun y ↦ c i * Complex.exp (A i y))
      ((c i * Complex.exp (A i z)) • A i) z := by
    intro i z
    simpa only [smul_smul] using ((A i).hasFDerivAt.cexp.const_mul (c i))
  intro x
  let R := ‖x‖ + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have hx : x ∈ Metric.ball (0 : E) R := by
    rw [mem_ball_zero_iff]
    dsimp [R]
    linarith
  apply (hasFDerivAt_tsum_of_isPreconnected (hs (R + 1)) Metric.isOpen_ball
    (convex_ball (0 : E) R).isPreconnected (fun i z _ ↦ hf i z)
    (fun i z hz ↦ b52_exponential_derivative_bound (A i) (c i) R z
      (mem_ball_zero_iff.mp hz).le)
    (x₀ := 0) (by simpa using hR) (by simpa using hc) hx).differentiableAt

#print axioms b52_differentiable_exponential_series

end HodgeLean.Foundations.Program
