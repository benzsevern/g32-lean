import HodgeLean.Foundations.Program.FuchsianSystemGaugeAnalytic
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Normed.Ring.InfiniteSum

noncomputable section
open Set Metric Filter
open scoped Topology NNReal
namespace HodgeLean.Foundations.Program

theorem b65f_series_derivative_hasSum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (p : FormalMultilinearSeries ℂ ℂ F) (hp : 0 < p.radius)
    {z : ℂ} (hz : z ∈ Metric.eball 0 p.radius) :
    HasSum (fun n ↦ z ^ n • ((n + 1) • p.coeff (n + 1))) (deriv p.sum z) := by
  have hd := (ContinuousLinearMap.apply ℂ F (1 : ℂ)).comp_hasFPowerSeriesOnBall
    (p.hasFPowerSeriesOnBall hp).fderiv
  have hh := hd.hasSum hz
  simpa only [zero_add, ContinuousLinearMap.compFormalMultilinearSeries_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply,
    ContinuousLinearMap.apply_apply, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    smul_apply, FormalMultilinearSeries.derivSeries_coeff_one,
    deriv] using hh

theorem b65f_powerSeries_product_hasSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (b c : ℕ → E →L[ℂ] E) (z : ℂ)
    (hb : Summable (fun n ↦ ‖z ^ n • b n‖))
    (hc : Summable (fun n ↦ ‖z ^ n • c n‖)) :
    HasSum (fun n ↦ z ^ n • ∑ i ∈ Finset.range (n + 1), b i * c (n - i))
      ((∑' n, z ^ n • b n) * ∑' n, z ^ n • c n) := by
  convert hasSum_sum_range_mul_of_summable_norm hb hc using 1
  funext n
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := by have := Finset.mem_range.mp hi; omega
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← pow_add, Nat.add_sub_of_le hi']

theorem b65f_gauge_identity_of_hasSum {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (R : E →L[ℂ] E) (b c : ℕ → E →L[ℂ] E) (z : ℂ)
    (B H D : E →L[ℂ] E)
    (hb : Summable (fun n ↦ ‖z ^ n • b n‖))
    (hc : Summable (fun n ↦ ‖z ^ n • c n‖))
    (hB : HasSum (fun n ↦ z ^ n • b n) B)
    (hH : HasSum (fun n ↦ z ^ n • c n) H)
    (hD : HasSum (fun n ↦ z ^ n • (((n + 1 : ℕ) : ℂ) • c (n + 1))) D)
    (hc0 : c 0 = 1)
    (hrec : ∀ n, ((n + 1 : ℕ) : ℂ) • c (n + 1) - (R * c (n + 1) - c (n + 1) * R) =
      ∑ i ∈ Finset.range (n + 1), b i * c (n - i)) :
    z • D = R * H - H * R + z • (B * H) := by
  have hcomm : HasSum (fun n ↦ z ^ n • (R * c n - c n * R)) (R * H - H * R) := by
    simpa only [mul_smul_comm, smul_mul_assoc, ← smul_sub] using
      (hH.mul_left R).sub (hH.mul_right R)
  have htail : HasSum (fun n ↦ z ^ (n + 1) • (R * c (n + 1) - c (n + 1) * R))
      (R * H - H * R) := by
    simpa [hc0] using (hasSum_nat_add_iff' 1).mpr hcomm
  have hprod := b65f_powerSeries_product_hasSum b c z hb hc
  rw [hB.tsum_eq, hH.tsum_eq] at hprod
  have hright := htail.add (hprod.const_smul z)
  have heq (n : ℕ) : z • (z ^ n • (((n + 1 : ℕ) : ℂ) • c (n + 1))) =
      z ^ (n + 1) • (R * c (n + 1) - c (n + 1) * R) +
        z • (z ^ n • ∑ i ∈ Finset.range (n + 1), b i * c (n - i)) := by
    calc
      _ = z ^ (n + 1) • (((n + 1 : ℕ) : ℂ) • c (n + 1)) := by
        rw [smul_smul, pow_succ']
      _ = z ^ (n + 1) • ((R * c (n + 1) - c (n + 1) * R) +
          ∑ i ∈ Finset.range (n + 1), b i * c (n - i)) := by
        congr 1
        exact (sub_eq_iff_eq_add.mp (hrec n)).trans (add_comm _ _)
      _ = _ := by rw [smul_add, smul_smul z, ← pow_succ']
  apply (hD.const_smul z).unique
  convert hright using 1
  funext n
  exact heq n

end HodgeLean.Foundations.Program
