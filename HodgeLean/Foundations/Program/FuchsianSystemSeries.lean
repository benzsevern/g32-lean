import HodgeLean.Foundations.Program.FuchsianSystemDefs
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.Normed

noncomputable section
open Set Metric
open scoped Interval
namespace HodgeLean.Foundations.Program

theorem b65f_iterated_norm_le (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (u v : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (u + (t : ℂ) * (v - u))‖ ≤ M)
    (m : ℕ) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖b65f_iterated E A u v m t‖ ≤ (‖v - u‖ * M) ^ m * t ^ m / m.factorial := by
  induction m generalizing t with
  | zero =>
    simpa only [b65f_iterated, pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one,
      div_one, ContinuousLinearMap.one_def] using
      (ContinuousLinearMap.norm_id_le (𝕜 := ℂ) (E := E))
  | succ m ih =>
    let K := ‖v - u‖ * M
    have hK : 0 ≤ K := mul_nonneg (norm_nonneg _) hM
    have hb (q : ℝ) (hq : q ∈ Ioc 0 t) :
        ‖(v - u) • (A (u + (q : ℂ) * (v - u)) * b65f_iterated E A u v m q)‖ ≤
          K * (K ^ m * q ^ m / m.factorial) := by
      have hq' : q ∈ Icc (0 : ℝ) 1 := ⟨hq.1.le, hq.2.trans ht.2⟩
      calc
        _ = ‖v - u‖ * ‖A (u + (q : ℂ) * (v - u)) * b65f_iterated E A u v m q‖ := norm_smul _ _
        _ ≤ ‖v - u‖ * (‖A (u + (q : ℂ) * (v - u))‖ * ‖b65f_iterated E A u v m q‖) :=
          mul_le_mul_of_nonneg_left (norm_mul_le _ _) (norm_nonneg _)
        _ ≤ ‖v - u‖ * (M * (K ^ m * q ^ m / m.factorial)) := by
          gcongr
          · exact hA q hq'
          · exact ih q hq'
        _ = _ := by dsimp [K]; ring
    have hi : IntervalIntegrable (fun q : ℝ ↦ K * (K ^ m * q ^ m / m.factorial))
        MeasureTheory.volume 0 t := by
      apply Continuous.intervalIntegrable
      fun_prop
    have he : (∫ q in (0 : ℝ)..t, K * (K ^ m * q ^ m / m.factorial)) =
        K ^ (m + 1) * t ^ (m + 1) / (m + 1).factorial := by
      simp only [div_eq_mul_inv, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_mul_const, integral_pow,
        zero_pow (Nat.succ_ne_zero m), sub_zero, Nat.factorial_succ,
        Nat.cast_mul, Nat.cast_add, Nat.cast_one]
      rw [pow_succ]
      field_simp
      ring
    exact (intervalIntegral.norm_integral_le_of_norm_le ht.1
      (Filter.Eventually.of_forall hb) hi).trans_eq he

theorem b65f_iterated_summable_of_bound (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (A : ℂ → E →L[ℂ] E) (u v : ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hA : ∀ t ∈ Icc (0 : ℝ) 1, ‖A (u + (t : ℂ) * (v - u))‖ ≤ M)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun m ↦ b65f_iterated E A u v m t) := by
  apply (Real.summable_pow_div_factorial ((‖v - u‖ * M) * t)).of_norm_bounded
  intro m
  simpa only [mul_pow, mul_assoc] using b65f_iterated_norm_le E A u v M hM hA m t ht

theorem b65f_iterated_initial (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (u v : ℂ) (m : ℕ) :
    b65f_iterated E A u v (m + 1) 0 = 0 := by
  simp only [b65f_iterated, intervalIntegral.integral_same]

theorem b65f_iterated_diagonal (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (u : ℂ) (m : ℕ) (t : ℝ) :
    b65f_iterated E A u u (m + 1) t = 0 := by
  simp [b65f_iterated]

theorem b65f_segment_initial (E : Type*) [NormedAddCommGroup E] [NormedSpace ℂ E]
    (A : ℂ → E →L[ℂ] E) (u : ℂ) : b65f_segment E A u u = 1 := by
  unfold b65f_segment
  rw [tsum_eq_single 0]
  · rfl
  · intro m hm
    obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    exact b65f_iterated_diagonal E A u m 1

theorem b65f_iterated_summable_of_continuousOn (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E]
    (A : ℂ → E →L[ℂ] E) (u v : ℂ)
    (hc : ContinuousOn (fun t : ℝ ↦ A (u + (t : ℂ) * (v - u))) (Icc 0 1))
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    Summable (fun m ↦ b65f_iterated E A u v m t) := by
  obtain ⟨M, hM, hb⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.exists_pos_norm_le
  apply b65f_iterated_summable_of_bound E A u v M hM.le _ t ht
  intro q hq
  exact hb _ (mem_image_of_mem _ hq)

theorem b65f_iterated_summable_on_disc (E : Type*) [NormedAddCommGroup E]
    [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (A : ℂ → E →L[ℂ] E) (a : ℂ) (r : ℝ) (hr : 0 < r)
    (hA : AnalyticOnNhd ℂ A (ball a r)) (z : ℂ) (hz : z ∈ ball a r) :
    Summable (fun m ↦ b65f_iterated E A a z m 1) := by
  letI : CompleteSpace E := FiniteDimensional.complete ℂ E
  apply b65f_iterated_summable_of_continuousOn E A a z _ 1 ⟨zero_le_one, le_rfl⟩
  apply hA.continuousOn.comp (by fun_prop)
  intro q hq
  simpa only [Complex.real_smul] using
    (convex_ball a r).add_smul_sub_mem (mem_ball_self hr) hz hq

end HodgeLean.Foundations.Program
