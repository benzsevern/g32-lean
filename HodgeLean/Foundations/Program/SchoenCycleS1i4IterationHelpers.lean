import HodgeLean.Foundations.Program.SchoenCycleS1i4Pre3Proofs

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

theorem s2e_remainder_summable_bound (d k : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (f : MvPowerSeries (Fin (d + 1)) ℂ)
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a)) :
    Summable (fun a => ‖MvPowerSeries.coeff a (s2e_divRemainder d k f)‖ *
      s2e_divWeight d r a) ∧
    s2e_divNorm d r (s2e_divRemainder d k f) ≤ s2e_divNorm d r f := by
  have hb (a : Fin (d + 1) →₀ ℕ) :
      ‖MvPowerSeries.coeff a (s2e_divRemainder d k f)‖ * s2e_divWeight d r a ≤
      ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a := by
    change ‖(if a (Fin.last d) < k then MvPowerSeries.coeff a f else 0)‖ * _ ≤ _
    split_ifs
    · exact le_rfl
    · simpa only [norm_zero, zero_mul] using mul_nonneg (norm_nonneg _)
        (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)
  have hs := hf.of_nonneg_of_le (fun a => mul_nonneg (norm_nonneg _)
    (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)) hb
  exact ⟨hs, hs.tsum_le_tsum hb hf⟩

theorem s2e_error_iterate_bound (d k : ℕ) (r : Fin (d + 1) → ℝ)
    (hr : ∀ i, 0 < r i) (e f : MvPowerSeries (Fin (d + 1)) ℂ)
    (he : Summable (fun a => ‖MvPowerSeries.coeff a e‖ * s2e_divWeight d r a))
    (hf : Summable (fun a => ‖MvPowerSeries.coeff a f‖ * s2e_divWeight d r a))
    (n : ℕ) :
    Summable (fun a => ‖MvPowerSeries.coeff a ((s2e_divError d k e)^[n] f)‖ *
      s2e_divWeight d r a) ∧
    s2e_divNorm d r ((s2e_divError d k e)^[n] f) ≤
      (s2e_divNorm d r e / r (Fin.last d) ^ k) ^ n * s2e_divNorm d r f := by
  have ht : 0 ≤ s2e_divNorm d r e / r (Fin.last d) ^ k :=
    div_nonneg (tsum_nonneg fun a => mul_nonneg (norm_nonneg _)
      (s2e_divWeight_nonneg d r (fun i => (hr i).le) a)) (pow_pos (hr _) _).le
  induction n with
  | zero => simpa only [Function.iterate_zero_apply, pow_zero, one_mul] using And.intro hf (le_refl (s2e_divNorm d r f))
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨_, _, hs, hb⟩ := s2e_s1i4_weighted_contraction_aux d k r hr e _ he ih.1
    refine ⟨hs, hb.trans ?_⟩
    calc
      _ ≤ (s2e_divNorm d r e / r (Fin.last d) ^ k) *
          ((s2e_divNorm d r e / r (Fin.last d) ^ k) ^ n * s2e_divNorm d r f) :=
        mul_le_mul_of_nonneg_left ih.2 ht
      _ = _ := by rw [pow_succ]; ring

theorem s2e_joint_summable_of_geometric {A : Type*}
    (u : ℕ → A → ℝ) (hu : ∀ n a, 0 ≤ u n a)
    (hs : ∀ n, Summable (u n)) (C θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1)
    (hb : ∀ n, (∑' a, u n a) ≤ θ ^ n * C) :
    Summable (fun na : ℕ × A => u na.1 na.2) := by
  apply (summable_prod_of_nonneg (fun na => hu na.1 na.2)).mpr
  refine ⟨hs, ?_⟩
  exact ((summable_geometric_of_lt_one hθ hθ1).mul_right C).of_nonneg_of_le
    (fun n => tsum_nonneg (hu n)) hb

end HodgeLean.Foundations.Program
