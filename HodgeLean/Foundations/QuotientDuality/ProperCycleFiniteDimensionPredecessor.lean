import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveHomologyDimension

/-! # Literal predecessor bounds for finite algebraic dimensions -/

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

/-- A literal algebraic dimension strictly below a natural dimension is bounded by its natural predecessor, including the empty-space value.
Source: WithBot.ne_bot_iff_exists; ENat.ne_top_iff_exists; Nat.le_pred_of_lt.
HC no distance; AV milestone no distance. -/
theorem properCycle_dimension_le_pred_of_lt (a : WithBot ℕ∞) (d : ℕ) (h : a < (d : ℕ)) :
    a ≤ (d-1 : ℕ) := by
  by_cases hb : a = ⊥
  · rw [hb]
    exact bot_le
  obtain ⟨b, rfl⟩ := WithBot.ne_bot_iff_exists.mp hb
  have hb' : b < (d : ℕ∞) := WithBot.coe_lt_coe.mp h
  obtain ⟨m, rfl⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hb')
  apply WithBot.coe_le_coe.mpr
  exact_mod_cast Nat.le_pred_of_lt (ENat.natCast_lt_natCast.mp hb')

end HodgeLean.Foundations.QuotientDuality
