import HodgeLean.Foundations.Program.SchoenCycleAdicIdealPowerValues
import Mathlib.RingTheory.PowerSeries.Trunc

/-! # Detecting formal maps by their polynomial values -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Maps from one variable series into an adic algebra agree when they agree
on polynomials and both send the coordinate into the extended adic ideal. -/
theorem s2e_c1_power_series_adic_algHom_ext
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    (J : Ideal R) (hJ : J.FG)
    (f g : PowerSeries k →ₐ[k] AdicCompletion J R)
    (hf : f PowerSeries.X ∈ J.map (algebraMap R (AdicCompletion J R)))
    (hg : g PowerSeries.X ∈ J.map (algebraMap R (AdicCompletion J R)))
    (h : ∀ p : Polynomial k, f (p : PowerSeries k) = g (p : PowerSeries k)) : f = g := by
  let K := J.map (algebraMap R (AdicCompletion J R))
  have htail (F : PowerSeries k →ₐ[k] AdicCompletion J R)
      (hF : F PowerSeries.X ∈ K) (z : PowerSeries k) (n : ℕ) :
      F z - F (z.trunc n : PowerSeries k) ∈ K ^ n := by
    have hz : z - (z.trunc n : PowerSeries k) =
        PowerSeries.X ^ n * PowerSeries.mk (fun i => z.coeff (i + n)) := by
      exact sub_eq_iff_eq_add.mpr (PowerSeries.eq_X_pow_mul_shift_add_trunc n z)
    rw [← map_sub, hz, map_mul, map_pow]
    exact (K ^ n).mul_mem_right _ (Ideal.pow_mem_pow hF n)
  apply AlgHom.ext
  intro z
  apply AdicCompletion.ext
  intro n
  have hf' := (s2e_adic_extended_power_mem_iff J hJ n _).mp (htail f hf z n)
  have hg' := (s2e_adic_extended_power_mem_iff J hJ n _).mp (htail g hg z n)
  change (f z).val n - (f (z.trunc n : PowerSeries k)).val n = 0 at hf'
  change (g z).val n - (g (z.trunc n : PowerSeries k)).val n = 0 at hg'
  rw [sub_eq_zero] at hf' hg'
  rw [hf', hg', h]

end HodgeLean.Foundations.Program
