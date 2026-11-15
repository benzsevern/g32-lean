import HodgeLean.Foundations.Program.SchoenCycleS1i4IterationHelpers

noncomputable section
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_weighted_family_coeff_summable
    (d : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (u : ℕ → MvPowerSeries (Fin (d + 1)) ℂ)
    (hu : Summable (fun na : ℕ × (Fin (d + 1) →₀ ℕ) =>
      ‖MvPowerSeries.coeff na.2 (u na.1)‖ * s2e_divWeight d r na.2))
    (a : Fin (d + 1) →₀ ℕ) : Summable (fun n => MvPowerSeries.coeff a (u n)) := by
  have hw : s2e_divWeight d r a ≠ 0 := ne_of_gt (Finset.prod_pos fun i _ => pow_pos (hr i) _)
  have hs := hu.comp_injective (show Function.Injective (fun n : ℕ => (n, a)) from
    fun _ _ h => (Prod.mk.inj h).1)
  exact ((summable_mul_right_iff hw).mp hs).of_norm

theorem s2e_pure_power_division (d k : ℕ)
    (f : MvPowerSeries (Fin (d + 1)) ℂ) :
    f = MvPowerSeries.X (Fin.last d) ^ k * s2e_divShift d k f +
      s2e_divRemainder d k f := by
  classical
  apply MvPowerSeries.ext
  intro a
  rw [map_add, MvPowerSeries.X_pow_eq, MvPowerSeries.coeff_monomial_mul]
  have hle : Finsupp.single (Fin.last d) k ≤ a ↔ k ≤ a (Fin.last d) :=
    Finsupp.single_le_iff
  by_cases h : k ≤ a (Fin.last d)
  · rw [if_pos (hle.mpr h), one_mul]
    change _ = MvPowerSeries.coeff ((a - Finsupp.single (Fin.last d) k) +
      Finsupp.single (Fin.last d) k) f + (if a (Fin.last d) < k then _ else 0)
    rw [tsub_add_cancel_of_le (hle.mpr h), if_neg (not_lt.mpr h), add_zero]
  · rw [if_neg (fun hh => h (hle.mp hh))]
    change _ = 0 + (if a (Fin.last d) < k then _ else 0)
    rw [if_pos (lt_of_not_ge h), zero_add]

theorem s2e_coeff_mul_sum (d : ℕ)
    (g : MvPowerSeries (Fin (d + 1)) ℂ)
    (u : ℕ → MvPowerSeries (Fin (d + 1)) ℂ)
    (hu : ∀ a, Summable (fun n => MvPowerSeries.coeff a (u n)))
    (a : Fin (d + 1) →₀ ℕ) :
    MvPowerSeries.coeff a (g * (show MvPowerSeries (Fin (d + 1)) ℂ from fun b => ∑' n, MvPowerSeries.coeff b (u n))) =
      ∑' n, MvPowerSeries.coeff a (g * u n) := by
  classical
  rw [MvPowerSeries.coeff_mul]
  simp only [MvPowerSeries.coeff_mul]
  change (∑ p ∈ Finset.antidiagonal a, MvPowerSeries.coeff p.1 g *
    ∑' n, MvPowerSeries.coeff p.2 (u n)) = _
  simp_rw [← tsum_mul_left]
  have ht : ∀ p ∈ Finset.antidiagonal a,
      Summable (fun n : ℕ => MvPowerSeries.coeff p.1 g * MvPowerSeries.coeff p.2 (u n)) :=
    fun p _ => (hu p.2).mul_left (MvPowerSeries.coeff p.1 g)
  exact (Summable.tsum_finsetSum ht).symm

theorem s2e_weighted_sum_summable
    (d : ℕ) (r : Fin (d + 1) → ℝ) (hr : ∀ i, 0 < r i)
    (u : ℕ → MvPowerSeries (Fin (d + 1)) ℂ)
    (hu : Summable (fun na : ℕ × (Fin (d + 1) →₀ ℕ) =>
      ‖MvPowerSeries.coeff na.2 (u na.1)‖ * s2e_divWeight d r na.2)) :
    Summable (fun a => ‖∑' n, MvPowerSeries.coeff a (u n)‖ * s2e_divWeight d r a) := by
  have hs := hu.prod_symm.prod
  apply hs.of_nonneg_of_le
  · intro a
    exact mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)
  · intro a
    change ‖∑' n, MvPowerSeries.coeff a (u n)‖ * s2e_divWeight d r a ≤
      ∑' n, ‖MvPowerSeries.coeff a (u n)‖ * s2e_divWeight d r a
    rw [tsum_mul_right]
    have hw : s2e_divWeight d r a ≠ 0 :=
      ne_of_gt (Finset.prod_pos fun i _ => pow_pos (hr i) _)
    have hna := hu.comp_injective (show Function.Injective (fun n : ℕ => (n, a)) from
        fun _ _ h => (Prod.mk.inj h).1)
    change Summable (fun n : ℕ =>
        ‖MvPowerSeries.coeff a (u n)‖ * s2e_divWeight d r a) at hna
    have hn := hna.div_const (s2e_divWeight d r a)
    simp only [mul_div_cancel_right₀ _ hw] at hn
    apply mul_le_mul_of_nonneg_right (norm_tsum_le_tsum_norm hn)
      (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)

theorem s2e_weighted_summable_mono (d : ℕ) (r R : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (hle : ∀ i, r i ≤ R i)
    (F : MvPowerSeries (Fin (d + 1)) ℂ)
    (hF : Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d R a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a F‖ * s2e_divWeight d r a) := by
  apply hF.of_nonneg_of_le
  · intro a
    exact mul_nonneg (norm_nonneg _) (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)
  · intro a
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    exact Finset.prod_le_prod₀ (fun i _ => (pow_pos (hr i) _).le)
      (fun i _ => pow_le_pow_left₀ (hr i).le (hle i) _)

end HodgeLean.Foundations.Program
