import HodgeLean.Foundations.Program.FuchsianSystemGaugeEquation
import Mathlib.Analysis.Normed.Ring.Units

noncomputable section
open Set Metric Filter
open scoped Topology NNReal
namespace HodgeLean.Foundations.Program

theorem b65f_seriesOfCoeff_sum_zero {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]
    (c : ℕ → F) : (b65f_seriesOfCoeff c).sum 0 = c 0 := by
  unfold FormalMultilinearSeries.sum
  simp only [b65f_seriesOfCoeff_apply]
  rw [tsum_eq_single 0]
  · simp
  · intro n hn
    simp [zero_pow hn]

theorem b65f_exists_analytic_gauge {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E]
    (R : E →L[ℂ] E) (B : ℂ → E →L[ℂ] E) (a : ℂ) (d : ℝ)
    (hd : 0 < d) (hB : AnalyticOnNhd ℂ B (ball a d))
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) :
    ∃ r : ℝ, 0 < r ∧ r ≤ d ∧ ∃ H : ℂ → E →L[ℂ] E,
      AnalyticOnNhd ℂ H (ball a r) ∧ H a = 1 ∧
      (∀ z ∈ ball a r, IsUnit (H z)) ∧
      ∀ z ∈ ball a r, (z - a) • deriv H z =
        R * H z - H z * R + (z - a) • (B z * H z) := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  obtain ⟨p, rp, hp⟩ := hB a (mem_ball_self hd)
  have hpr : 0 < p.radius := hp.r_pos.trans_le hp.r_le
  obtain ⟨M, S, hM, hS, hb⟩ := p.le_mul_pow_of_radius_pos hpr
  obtain ⟨C, hC, hinv⟩ := b65f_gaugeOperator_uniform_bound R hnr
  let b := p.coeff
  let c := b65f_gaugeCoeff R b hnr
  let q := b65f_seriesOfCoeff c
  have hbc (n : ℕ) : ‖b n‖ ≤ M * S ^ n := by
    change ‖p.coeff n‖ ≤ M * S ^ n
    rw [← p.norm_apply_eq_norm_coef]
    exact hb n
  have hqc : 0 < q.radius := b65f_seriesOfCoeff_radius_pos c (S + C * M)
    (by positivity) (b65f_gaugeCoeff_geometric_bound R b hnr C M S hC hM.le hS.le hinv hbc)
  have hq := q.hasFPowerSeriesOnBall hqc
  let H : ℂ → E →L[ℂ] E := fun z ↦ q.sum (z - a)
  have hH0 : H a = 1 := by
    simp only [H, sub_self]
    exact (b65f_seriesOfCoeff_sum_zero c).trans (b65f_gaugeCoeff_zero R b hnr)
  have hHa : AnalyticAt ℂ H a := by
    have hh : AnalyticAt ℂ q.sum (a - a) := by simpa using hq.analyticAt
    exact hh.comp (f := fun z : ℂ ↦ z - a) (analyticAt_id.sub analyticAt_const)
  have hzB : ∀ᶠ z in 𝓝 a, z - a ∈ Metric.eball 0 rp := by
    apply (show ContinuousAt (fun z : ℂ ↦ z - a) a from by fun_prop).preimage_mem_nhds
    simpa only [sub_self] using Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hp.r_pos)
  have hzG : ∀ᶠ z in 𝓝 a, z - a ∈ Metric.eball 0 q.radius := by
    apply (show ContinuousAt (fun z : ℂ ↦ z - a) a from by fun_prop).preimage_mem_nhds
    simpa only [sub_self] using Metric.isOpen_eball.mem_nhds (Metric.mem_eball_self hqc)
  have hu : ∀ᶠ z in 𝓝 a, IsUnit (H z) := by
    change H ⁻¹' {w | IsUnit w} ∈ 𝓝 a
    apply hHa.continuousAt.preimage_mem_nhds
    rw [hH0]
    exact Units.isOpen.mem_nhds isUnit_one
  have heq : ∀ᶠ z in 𝓝 a, (z - a) • deriv H z =
      R * H z - H z * R + (z - a) • (B z * H z) := by
    filter_upwards [hzB, hzG] with z hzB hzG
    have hpz := hp.hasSum hzB
    have hqz := hq.hasSum hzG
    have hdb := b65f_series_derivative_hasSum q hqc hzG
    have hdc : HasDerivAt H (deriv q.sum (z - a)) z := by
      simpa only [H, Function.comp_def, id_eq, one_smul] using
        (hq.analyticAt_of_mem hzG).differentiableAt.hasDerivAt.scomp z
          ((hasDerivAt_id z).sub_const a)
    have hbn := p.summable_norm_apply ((Metric.eball_subset_eball hp.r_le) hzB)
    have hcn := q.summable_norm_apply hzG
    have hcoeff (n : ℕ) : q.coeff n = c n := by
      simp [q, b65f_seriesOfCoeff, FormalMultilinearSeries.coeff]
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, add_sub_cancel] at hpz
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff, zero_add] at hqz
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff] at hbn
    simp only [FormalMultilinearSeries.apply_eq_pow_smul_coeff, hcoeff] at hcn
    simp only [hcoeff, ← Nat.cast_smul_eq_nsmul ℂ] at hdb
    rw [hdc.deriv]
    exact b65f_gauge_identity_of_hasSum R b c (z - a) (B z) (H z) _ hbn hcn hpz hqz hdb
      (b65f_gaugeCoeff_zero R b hnr) (b65f_gaugeCoeff_recurrence R b hnr)
  obtain ⟨r, hr, hgood⟩ := Metric.eventually_nhds_iff.mp
    (hHa.eventually_analyticAt.and (hu.and heq))
  refine ⟨min r d, lt_min hr hd, min_le_right _ _, H, ?_, hH0, ?_, ?_⟩
  · exact fun z hz ↦ (hgood ((ball_subset_ball (min_le_left _ _)) hz)).1
  · exact fun z hz ↦ (hgood ((ball_subset_ball (min_le_left _ _)) hz)).2.1
  · exact fun z hz ↦ (hgood ((ball_subset_ball (min_le_left _ _)) hz)).2.2

end HodgeLean.Foundations.Program
