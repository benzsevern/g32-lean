import HodgeLean.Foundations.Program.FuchsianSystemGaugeMajorant
import Mathlib.Analysis.Analytic.ChangeOrigin

noncomputable section
open Set Metric
open scoped NNReal
namespace HodgeLean.Foundations.Program

def b65f_seriesOfCoeff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (c : ℕ → F) : FormalMultilinearSeries ℂ ℂ F :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (c n)

theorem b65f_seriesOfCoeff_apply {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (c : ℕ → F) (n : ℕ) (z : ℂ) :
    b65f_seriesOfCoeff c n (fun _ ↦ z) = z ^ n • c n := by
  simp [b65f_seriesOfCoeff, ContinuousMultilinearMap.mkPiRing_apply]

theorem b65f_seriesOfCoeff_analytic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    [CompleteSpace F] (c : ℕ → F) (D : ℝ) (hD : 0 ≤ D)
    (hb : ∀ n, ‖c n‖ ≤ D ^ n) :
    AnalyticOnNhd ℂ (b65f_seriesOfCoeff c).sum (ball 0 (1 / (D + 1))) := by
  let r : ℝ≥0 := ⟨1 / (D + 1), by positivity⟩
  have hrval : (r : ℝ) = 1 / (D + 1) := rfl
  have hr : 0 < r := by
    change (0 : ℝ) < 1 / (D + 1)
    positivity
  have hle : (r : ENNReal) ≤ (b65f_seriesOfCoeff c).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro n
    calc
      ‖b65f_seriesOfCoeff c n‖ * (r : ℝ) ^ n ≤ D ^ n * (r : ℝ) ^ n := by
        gcongr
        simpa only [b65f_seriesOfCoeff, ContinuousMultilinearMap.norm_mkPiRing] using hb n
      _ = (D * (r : ℝ)) ^ n := (mul_pow _ _ _).symm
      _ ≤ 1 := by
        apply pow_le_one₀ (by positivity)
        rw [hrval, mul_one_div, div_le_one (by positivity : 0 < D + 1)]
        linarith
  have hp := (b65f_seriesOfCoeff c).hasFPowerSeriesOnBall
    ((ENNReal.coe_pos.mpr hr).trans_le hle)
  intro z hz
  have hz' : z ∈ Metric.eball (0 : ℂ) (r : ENNReal) := by
    rw [Metric.eball_coe, hrval]
    exact hz
  exact hp.analyticAt_of_mem ((Metric.eball_subset_eball hle) hz')

theorem b65f_seriesOfCoeff_radius_pos {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (c : ℕ → F) (D : ℝ) (hD : 0 ≤ D) (hb : ∀ n, ‖c n‖ ≤ D ^ n) :
    0 < (b65f_seriesOfCoeff c).radius := by
  let r : ℝ≥0 := ⟨1 / (D + 1), by positivity⟩
  have hrval : (r : ℝ) = 1 / (D + 1) := rfl
  have hr : 0 < r := by
    change (0 : ℝ) < 1 / (D + 1)
    positivity
  have hle : (r : ENNReal) ≤ (b65f_seriesOfCoeff c).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ 1
    intro n
    calc
      ‖b65f_seriesOfCoeff c n‖ * (r : ℝ) ^ n ≤ D ^ n * (r : ℝ) ^ n := by
        gcongr
        simpa only [b65f_seriesOfCoeff, ContinuousMultilinearMap.norm_mkPiRing] using hb n
      _ = (D * (r : ℝ)) ^ n := (mul_pow _ _ _).symm
      _ ≤ 1 := by
        apply pow_le_one₀ (by positivity)
        rw [hrval, mul_one_div, div_le_one (by positivity : 0 < D + 1)]
        linarith
  exact (ENNReal.coe_pos.mpr hr).trans_le hle

theorem b65f_gaugeSeries_analytic {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E]
    (R : E →L[ℂ] E) (b : ℕ → E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R)))
    (C M S : ℝ) (hC : 1 ≤ C) (hM : 0 ≤ M) (hS : 0 ≤ S)
    (hinv : ∀ k : ℕ, 0 < k → ∀ T : E →L[ℂ] E,
      ‖T‖ ≤ C * ‖(k : ℂ) • T - (R * T - T * R)‖)
    (hb : ∀ n, ‖b n‖ ≤ M * S ^ n) :
    AnalyticOnNhd ℂ (b65f_seriesOfCoeff (b65f_gaugeCoeff R b hnr)).sum
      (ball 0 (1 / (S + C * M + 1))) := by
  apply b65f_seriesOfCoeff_analytic _ _ (by positivity)
  exact b65f_gaugeCoeff_geometric_bound R b hnr C M S hC hM hS hinv hb

end HodgeLean.Foundations.Program
