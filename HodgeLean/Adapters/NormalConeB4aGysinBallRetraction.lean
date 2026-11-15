import HodgeLean.Adapters.NormalConeB4aGysinSupportTrapping

noncomputable section
namespace HodgeLean.Adapters

/-- A nonnegative closed ball has a continuous radial retraction fixing
all vectors of norm at most its radius. -/
theorem a3b4a_gysin_exists_closedBall_retraction
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (r : ℝ) (hr : 0 ≤ r) :
    ∃ F : C(E, E), (∀ x, ‖F x‖ ≤ r) ∧ ∀ x, ‖x‖ ≤ r → F x = x := by
  rcases eq_or_lt_of_le hr with hr0 | hrpos
  · subst r
    refine ⟨0, ?_, ?_⟩
    · intro x
      simp only [ContinuousMap.zero_apply, norm_zero, le_refl]
    · intro x hx
      have hx0 : x = 0 := norm_eq_zero.mp (le_antisymm hx (norm_nonneg x))
      simpa only [ContinuousMap.zero_apply, hx0]
  · have hmax (x : E) : 0 < max r ‖x‖ := lt_of_lt_of_le hrpos (le_max_left _ _)
    let F : C(E, E) := ⟨fun x => (r / max r ‖x‖) • x,
      (continuous_const.div (continuous_const.max continuous_norm)
        (fun x => ne_of_gt (hmax x))).smul continuous_id⟩
    refine ⟨F, ?_, ?_⟩
    · intro x
      change ‖(r / max r ‖x‖) • x‖ ≤ r
      rw [norm_smul, Real.norm_of_nonneg (div_nonneg hrpos.le (hmax x).le), div_mul_eq_mul_div]
      apply (div_le_iff₀ (hmax x)).mpr
      exact mul_le_mul_of_nonneg_left (le_max_right r ‖x‖) hrpos.le
    · intro x hx
      change (r / max r ‖x‖) • x = x
      rw [max_eq_left hx, div_self hrpos.ne', one_smul]

end HodgeLean.Adapters
