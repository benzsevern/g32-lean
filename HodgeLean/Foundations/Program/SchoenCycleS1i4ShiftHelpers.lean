import HodgeLean.Foundations.Program.SchoenCycleS1i4WeightHelpers

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_divWeight_single (d k : ℕ) (r : Fin (d + 1) → ℝ) :
    s2e_divWeight d r (Finsupp.single (Fin.last d) k) = r (Fin.last d) ^ k := by
  classical
  simp [s2e_divWeight, Finsupp.single_apply]

theorem s2e_shift_weight_identity (d k : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (a : Fin (d + 1) →₀ ℕ) :
    ‖MvPowerSeries.coeff a (s2e_divShift d k f)‖ * s2e_divWeight d r a =
      (‖MvPowerSeries.coeff (a + Finsupp.single (Fin.last d) k) f‖ *
        s2e_divWeight d r (a + Finsupp.single (Fin.last d) k)) /
          r (Fin.last d) ^ k := by
  change ‖MvPowerSeries.coeff (a + Finsupp.single (Fin.last d) k) f‖ * _ = _
  rw [s2e_divWeight_add, s2e_divWeight_single]
  rw [← mul_assoc, mul_div_cancel_right₀ _ (pow_ne_zero _ (ne_of_gt (hr _)))]

theorem s2e_shift_summable_bound (d k : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a (s2e_divShift d k f)‖ *
      s2e_divWeight d r a) ∧
    s2e_divNorm d r (s2e_divShift d k f) ≤ s2e_divNorm d r f / r (Fin.last d) ^ k := by
  let u := fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a
  let t := Finsupp.single (Fin.last d) k
  have hi : Function.Injective (fun a : Fin (d + 1) →₀ ℕ => a + t) :=
    add_left_injective t
  have hs : Summable (fun a => u (a + t)) := hf.comp_injective hi
  have hn (a) : 0 ≤ u a := mul_nonneg (norm_nonneg _)
    (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)
  have hb : (∑' a, u (a + t)) ≤ ∑' a, u a := tsum_comp_le_tsum_of_inj hf hn hi
  have heq : (fun a => ‖MvPowerSeries.coeff a (s2e_divShift d k f)‖ *
      s2e_divWeight d r a) = fun a => u (a + t) / r (Fin.last d) ^ k := by
    funext a
    exact s2e_shift_weight_identity d k r hr f a
  constructor
  · rw [heq]
    exact hs.div_const _
  · change (∑' a, ‖MvPowerSeries.coeff a (s2e_divShift d k f)‖ *
        s2e_divWeight d r a) ≤ _
    rw [heq, tsum_div_const]
    exact div_le_div_of_nonneg_right hb (pow_pos (hr _) _).le

end HodgeLean.Foundations.Program
