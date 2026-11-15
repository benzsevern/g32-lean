module

public import HodgeLean.Foundations.Program.SchoenCycleS1i4MonomialHelpers
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
import all Mathlib.Basic.Complex.Basic

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_weighted_smul_summable (d : ℕ) (r : Fin (d + 1) → ℝ)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a)) (c : ℂ) :
    Summable (fun a => ‖MvPowerSeries.coeff a (c • F)‖ * s2e_divWeight d r a) := by
  convert hF.mul_left ‖c‖ using 1
  funext a
  simp only [map_smul, norm_smul, smul_eq_mul, norm_mul]
  ring

theorem s2e_weighted_sub_summable (d : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (F G : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a))
    (hG : Summable (fun a => ‖MvPowerSeries.coeff a G‖ * s2e_divWeight d r a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a (F - G)‖ * s2e_divWeight d r a) := by
  apply (hF.add hG).of_nonneg_of_le
  · intro a
    exact mul_nonneg (norm_nonneg _) (Finset.prod_nonneg fun i _ => (pow_pos (hr i) _).le)
  · intro a
    rw [map_sub, ← add_mul]
    exact mul_le_mul_of_nonneg_right (norm_sub_le _ _)
      (Finset.prod_nonneg fun i _ => (pow_pos (hr i) _).le)

theorem s2e_weighted_X_pow_summable (d k : ℕ) (r : Fin (d + 1) → ℝ) :
    Summable (fun a => ‖MvPowerSeries.coeff a (MvPowerSeries.X (Fin.last d) ^ k :
      MvPowerSeries (Fin (d + 1)) ℂ)‖ * s2e_divWeight d r a) := by
  classical
  apply summable_of_hasFiniteSupport
  apply Set.Finite.subset (Set.finite_singleton (Finsupp.single (Fin.last d) k))
  intro a ha
  by_contra h
  have hne : a ≠ Finsupp.single (Fin.last d) k := by simpa using h
  have hz : MvPowerSeries.coeff a (MvPowerSeries.X (Fin.last d) ^ k :
      MvPowerSeries (Fin (d + 1)) ℂ) = 0 := by
    rw [MvPowerSeries.coeff_X_pow, if_neg hne]
  simpa only [Function.mem_support, hz, norm_zero, zero_mul, ne_eq, not_true_eq_false] using ha

theorem s2e_divSeries_smul (m : ℕ) (F : MvPowerSeries (Fin m) ℂ) (c : ℂ) (z : Fin m → ℂ) :
    s2e_divSeries m (c • F) z = c * s2e_divSeries m F z := by
  unfold s2e_divSeries
  simp only [map_smul, smul_eq_mul, mul_assoc, tsum_mul_left]

end HodgeLean.Foundations.Program
