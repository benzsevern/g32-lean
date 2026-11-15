import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Analytic.IsolatedZeros

/-! # Taylor remainders for collision traces -/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators Topology
namespace HodgeLean.Foundations.Program.G32Native

/-- Repeated divided differences at the collision point. -/
def collisionTaylorRemainder (H : ℂ → ℂ) (n : ℕ) : ℂ → ℂ :=
  (Function.swap dslope 0)^[n] H

/-- Each divided difference gives the next exact remainder. -/
theorem collisionTaylorRemainder_step (H : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    collisionTaylorRemainder H n z = collisionTaylorRemainder H n 0 +
      z * collisionTaylorRemainder H (n + 1) z := by
  have he := sub_smul_dslope (collisionTaylorRemainder H n) (0 : ℂ) z
  have hs : collisionTaylorRemainder H (n + 1) = dslope (collisionTaylorRemainder H n) 0 := by
    simp only [collisionTaylorRemainder, Function.iterate_succ_apply']
  rw [hs]
  simpa only [sub_zero, smul_eq_mul, sub_eq_iff_eq_add, add_comm] using he.symm

/-- The Taylor polynomial and its divided-difference remainder are an exact identity. -/
theorem collisionTaylorRemainder_expansion (H : ℂ → ℂ) (n : ℕ) (z : ℂ) :
    H z = (∑ j ∈ Finset.range n, z ^ j * collisionTaylorRemainder H j 0) +
      z ^ n * collisionTaylorRemainder H n z := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, collisionTaylorRemainder,
      Function.iterate_zero, id_eq, pow_zero, one_mul, zero_add]
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc
      H z = (∑ j ∈ Finset.range n, z ^ j * collisionTaylorRemainder H j 0) +
          z ^ n * collisionTaylorRemainder H n z := ih
      _ = _ := by rw [collisionTaylorRemainder_step H n z, pow_succ]; ring

/-- An analytic remainder is continuous at the collision point. -/
theorem collisionTaylorRemainder_continuousAt {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt H p 0) (n : ℕ) :
    ContinuousAt (collisionTaylorRemainder H n) 0 :=
  (hp.has_fpower_series_iterate_dslope_fslope n).continuousAt

/-- The value of the analytic remainder is the specified Taylor coefficient. -/
theorem collisionTaylorRemainder_zero {H : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} (hp : HasFPowerSeriesAt H p 0) (n : ℕ) :
    collisionTaylorRemainder H n 0 = p.coeff n := by
  have he := ((hp.has_fpower_series_iterate_dslope_fslope n).coeff_zero 1).symm
  change collisionTaylorRemainder H n 0 = (FormalMultilinearSeries.fslope^[n] p).coeff 0 at he
  simpa only [FormalMultilinearSeries.coeff_iterate_fslope, zero_add] using he

#print axioms collisionTaylorRemainder_step
#print axioms collisionTaylorRemainder_expansion
#print axioms collisionTaylorRemainder_continuousAt
#print axioms collisionTaylorRemainder_zero
end HodgeLean.Foundations.Program.G32Native
