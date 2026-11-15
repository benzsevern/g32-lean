import HodgeLean.Foundations.Program.FuchsianSystemGauge

noncomputable section
namespace HodgeLean.Foundations.Program

def b65f_gaugeOperator {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R : E →L[ℂ] E) (k : ℕ) : (E →L[ℂ] E) →L[ℂ] (E →L[ℂ] E) :=
  (k : ℂ) • ContinuousLinearMap.id ℂ (E →L[ℂ] E) -
    (ContinuousLinearMap.mul ℂ (E →L[ℂ] E) R -
      (ContinuousLinearMap.mul ℂ (E →L[ℂ] E)).flip R)

theorem b65f_gaugeOperator_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (R T : E →L[ℂ] E) (k : ℕ) :
    b65f_gaugeOperator R k T = (k : ℂ) • T - (R * T - T * R) := rfl

theorem b65f_gaugeOperator_uniform_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (R : E →L[ℂ] E)
    (hnr : ∀ k : ℕ, 0 < k → Function.Bijective
      (fun T : E →L[ℂ] E ↦ (k : ℂ) • T - (R * T - T * R))) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ k : ℕ, 0 < k → ∀ T : E →L[ℂ] E,
      ‖T‖ ≤ C * ‖(k : ℂ) • T - (R * T - T * R)‖ := by
  have hpoint (k : ℕ) (hk : 0 < k) : ∃ C : ℝ, 1 ≤ C ∧
      ∀ T : E →L[ℂ] E, ‖T‖ ≤ C * ‖b65f_gaugeOperator R k T‖ := by
    obtain ⟨K, _, hK⟩ := (b65f_gaugeOperator R k).toLinearMap.injective_iff_antilipschitz.mp
      (hnr k hk).injective
    refine ⟨max 1 K, le_max_left _ _, fun T ↦ ?_⟩
    exact (hK.le_mul_norm (map_zero _) T).trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hfinite (N : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ k ≤ N, 0 < k →
      ∀ T : E →L[ℂ] E, ‖T‖ ≤ C * ‖b65f_gaugeOperator R k T‖ := by
    induction N with
    | zero => exact ⟨1, le_rfl, by intro k hk hpos; omega⟩
    | succ N ih =>
      obtain ⟨C, hC, hb⟩ := ih
      obtain ⟨D, hD, hd⟩ := hpoint (N + 1) (Nat.succ_pos N)
      refine ⟨max C D, hC.trans (le_max_left _ _), ?_⟩
      intro k hk hkpos T
      rcases Nat.eq_or_lt_of_le hk with rfl | hk'
      · exact (hd T).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
      · exact (hb k (by omega) hkpos T).trans
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  obtain ⟨N, hN⟩ := exists_nat_gt (4 * ‖R‖ + 2)
  obtain ⟨C, hC, hb⟩ := hfinite N
  refine ⟨C, hC, ?_⟩
  intro k hk T
  by_cases hkN : k ≤ N
  · exact hb k hkN hk T
  · have hkR : (N : ℝ) < k := by exact_mod_cast (show N < k by omega)
    have hlarge : 4 * ‖R‖ < (k : ℝ) := by linarith
    have htwo : 2 ≤ (k : ℝ) := by linarith [norm_nonneg R]
    have hdiv : 2 / (k : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr htwo
    exact (b65f_gaugeOperator_large_bound R T k hlarge).trans
      (mul_le_mul_of_nonneg_right (hdiv.trans hC) (norm_nonneg _))

end HodgeLean.Foundations.Program
