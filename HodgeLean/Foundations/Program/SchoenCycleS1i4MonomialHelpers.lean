module

public import HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionSeries
import all HodgeLean.Foundations.Program.SchoenCycleDivisionCoefficients
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Ring

public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Filter Topology
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_monomial_norm_summable (d : ℕ) (r : Fin (d + 1) → ℝ)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a))
    (z : Fin (d + 1) → ℂ) (hz : ∀ i, ‖z i‖ ≤ r i) :
    Summable (fun a => ‖MvPowerSeries.coeff a F * ∏ i, z i ^ a i‖) := by
  apply hF.of_nonneg_of_le (fun a => norm_nonneg _)
  intro a
  simp only [norm_mul, norm_prod, norm_pow, s2e_divWeight]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  exact Finset.prod_le_prod₀ (fun i _ => pow_nonneg (norm_nonneg _) _)
    (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hz i) _)

theorem s2e_eventually_polydisc (d : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) :
    ∀ᶠ z in nhds (0 : Fin (d + 1) → ℂ), ∀ i, ‖z i‖ ≤ r i := by
  apply eventually_all.mpr
  intro i
  have hc : ContinuousAt (fun z : Fin (d + 1) → ℂ => ‖z i‖) 0 :=
    (continuous_apply i).continuousAt.norm
  exact (hc.eventually (gt_mem_nhds (by simpa using hr i))).mono fun z hz => hz.le

theorem s2e_divSeries_mul_at (m : ℕ) (G Q : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ)
    (hG : Summable (fun a => ‖MvPowerSeries.coeff a G * ∏ i, z i ^ a i‖))
    (hQ : Summable (fun a => ‖MvPowerSeries.coeff a Q * ∏ i, z i ^ a i‖)) :
    s2e_divSeries m (G * Q) z = s2e_divSeries m G z * s2e_divSeries m Q z := by
  classical
  unfold s2e_divSeries
  rw [hG.of_norm.tsum_mul_tsum_eq_tsum_sum_antidiagonal hQ.of_norm
    (summable_mul_of_summable_norm
      (f := fun a => MvPowerSeries.coeff a G * ∏ i, z i ^ a i)
      (g := fun a => MvPowerSeries.coeff a Q * ∏ i, z i ^ a i) hG hQ)]
  apply tsum_congr
  intro a
  rw [MvPowerSeries.coeff_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  have hp' : p.1 + p.2 = a := Finset.mem_antidiagonal.mp hp
  rw [← hp']
  simp only [Finsupp.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

theorem s2e_divSeries_add_at (m : ℕ) (G B : MvPowerSeries (Fin m) ℂ)
    (z : Fin m → ℂ)
    (hG : Summable (fun a => MvPowerSeries.coeff a G * ∏ i, z i ^ a i))
    (hB : Summable (fun a => MvPowerSeries.coeff a B * ∏ i, z i ^ a i)) :
    s2e_divSeries m (G + B) z = s2e_divSeries m G z + s2e_divSeries m B z := by
  unfold s2e_divSeries
  simp only [map_add, add_mul]
  exact hG.tsum_add hB

end HodgeLean.Foundations.Program
