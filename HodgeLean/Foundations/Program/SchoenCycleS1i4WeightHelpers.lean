import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import HodgeLean.Foundations.Program.SchoenCycleS1i4ConvolutionHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_divWeight_nonneg (d : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 ≤ r i) (a : Fin (d + 1) →₀ ℕ) : 0 ≤ s2e_divWeight d r a :=
  by
    unfold s2e_divWeight
    exact Finset.prod_nonneg fun i _ => pow_nonneg (hr i) _

theorem s2e_divWeight_add (d : ℕ) (r : Fin (d + 1) → ℝ)
    (a b : Fin (d + 1) →₀ ℕ) :
    s2e_divWeight d r (a + b) = s2e_divWeight d r a * s2e_divWeight d r b := by
  simp only [s2e_divWeight, Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]

theorem s2e_weighted_product_bound (d : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 ≤ r i) (e f : MvPowerSeries (Fin (d + 1)) ℂ)
    (a : Fin (d + 1) →₀ ℕ) :
    ‖MvPowerSeries.coeff a (e * f)‖ * s2e_divWeight d r a ≤
      ∑ p ∈ Finset.antidiagonal a,
        (‖MvPowerSeries.coeff p.1 e‖ * s2e_divWeight d r p.1) *
        (‖MvPowerSeries.coeff p.2 f‖ * s2e_divWeight d r p.2) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  calc
    _ ≤ (∑ p ∈ Finset.antidiagonal a,
        ‖MvPowerSeries.coeff p.1 e * MvPowerSeries.coeff p.2 f‖) *
          s2e_divWeight d r a :=
      mul_le_mul_of_nonneg_right (norm_sum_le _ _) (s2e_divWeight_nonneg d r hr a)
    _ = _ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      have hp' : p.1 + p.2 = a := Finset.mem_antidiagonal.mp hp
      rw [← hp', s2e_divWeight_add, norm_mul]
      ring

theorem s2e_weighted_mul_summable (d : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 ≤ r i) (e f : MvPowerSeries (Fin (d + 1)) ℂ)
    (he : Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a))
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a (e * f)‖ * s2e_divWeight d r a) ∧
    s2e_divNorm d r (e * f) ≤ s2e_divNorm d r e * s2e_divNorm d r f := by
  classical
  have hn (g : MvPowerSeries (Fin (d + 1)) ℂ) (a : Fin (d + 1) →₀ ℕ) :
      0 ≤ ‖MvPowerSeries.coeff a g‖ * s2e_divWeight d r a :=
    mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r hr a)
  exact s2e_summable_convolution_majorant _ _ _ he hf (hn e) (hn f) (hn (e * f))
    (s2e_weighted_product_bound d r hr e f)

end HodgeLean.Foundations.Program
