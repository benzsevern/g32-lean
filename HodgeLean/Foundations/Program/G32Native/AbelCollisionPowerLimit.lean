import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Derivative limits along monic coefficient paths -/
noncomputable section
set_option maxHeartbeats 400000
open Filter
open scoped Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- A positive power path remains in the punctured coefficient neighbourhood. -/
theorem collision_negative_power_tendsto {n : ℕ} (hn : 0 < n) :
    Tendsto (fun t : ℂ => -(t ^ n)) (𝓝[≠] 0) (𝓝[≠] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : ContinuousAt (fun t : ℂ => -(t ^ n)) 0 :=
      (continuousAt_id.pow n).neg
    simpa only [zero_pow (Nat.ne_of_gt hn), neg_zero] using
      hc.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact neg_ne_zero.mpr (pow_ne_zero n ht)

/-- Dividing the coefficient-path variation by the root parameter power gives the negative derivative. -/
theorem collision_negative_power_slope_limit {n : ℕ} (hn : 0 < n)
    {G : ℂ → ℂ} {d : ℂ} (hG : HasDerivAt G d 0) :
    Tendsto (fun t : ℂ => (G (-(t ^ n)) - G 0) / t ^ n)
      (𝓝[≠] 0) (𝓝 (-d)) := by
  have he := hG.tendsto_slope_zero.comp (collision_negative_power_tendsto hn)
  have hn' := he.neg
  simpa only [Function.comp_def, zero_add, smul_eq_mul, inv_neg, neg_mul,
    neg_neg, div_eq_mul_inv, mul_comm] using hn'

#print axioms collision_negative_power_tendsto
#print axioms collision_negative_power_slope_limit
end HodgeLean.Foundations.Program.G32Native
