import HodgeLean.Foundations.Program.FuchsianSystemGaugeExistence
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open Set Metric
namespace HodgeLean.Foundations.Program

theorem b65f_gauge_derivative_rescale {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (B H : ℂ → E →L[ℂ] E) (a z : ℂ) (hz : z - a ≠ 0)
    (hg : (z - a) • deriv H z = R * H z - H z * R + (z - a) • (B z * H z)) :
    deriv H z = (z - a)⁻¹ • (R * H z - H z * R) + B z * H z := by
  have hh := congrArg (fun T : E →L[ℂ] E ↦ (z - a)⁻¹ • T) hg
  simpa only [smul_add, smul_smul, inv_mul_cancel₀ hz, one_smul] using hh

theorem b65f_slit_solution_hasDerivAt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (R : E →L[ℂ] E) (B H : ℂ → E →L[ℂ] E) (a z : ℂ)
    (hH : DifferentiableAt ℂ H z) (hz : z - a ∈ Complex.slitPlane)
    (hg : (z - a) • deriv H z = R * H z - H z * R + (z - a) • (B z * H z)) :
    HasDerivAt (fun w ↦ H w * NormedSpace.exp (Complex.log (w - a) • R))
      (((z - a)⁻¹ • R + B z) * (H z * NormedSpace.exp (Complex.log (z - a) • R))) z := by
  have hw : z - a ≠ 0 := Complex.slitPlane_ne_zero hz
  have hl : HasDerivAt (fun w : ℂ ↦ Complex.log (w - a)) (z - a)⁻¹ z := by
    simpa only [mul_one, Function.comp_def, id_eq] using (Complex.hasDerivAt_log hz).comp z ((hasDerivAt_id z).sub_const a)
  have he := (hasDerivAt_exp_smul_const' R (Complex.log (z - a))).scomp z hl
  have hh := hH.hasDerivAt.mul he
  convert hh using 1
  · funext w
    rfl
  · simp only [Pi.mul_apply, Function.comp_apply]
    rw [b65f_gauge_derivative_rescale R B H a z hw hg]
    simp only [add_mul, smul_mul_assoc, smul_sub, sub_mul, mul_smul_comm, mul_assoc]
    abel

end HodgeLean.Foundations.Program
