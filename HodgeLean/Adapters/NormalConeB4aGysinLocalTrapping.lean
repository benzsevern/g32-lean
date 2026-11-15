import HodgeLean.Adapters.NormalConeB4aGysinDegreeDeformation
import Mathlib.Topology.Order.Compact

/-! # Compact trapping near an isolated zero

An isolated zero has a positive norm bound on a compact annulus. Small
translations therefore keep their zeros inside a smaller compact ball.
-/

noncomputable section
namespace HodgeLean.Adapters

/-- A continuous map avoiding zero on a compact set has a positive uniform
lower bound for its norm on that set, including when the set is empty. -/
theorem a3b4a_gysin_compact_norm_lower_bound
    {X E : Type*} [TopologicalSpace X] [NormedAddCommGroup E]
    (f : C(X, E)) (K : Set X) (hK : IsCompact K)
    (hf : ∀ x ∈ K, f x ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ x ∈ K, ε ≤ ‖f x‖ := by
  exact hK.exists_forall_le' f.continuous.norm.continuousOn
    (fun x hx => norm_pos_iff.mpr (hf x hx))

/-- An isolated zero on an outer ball traps every small straight-line
translation inside any smaller positive-radius ball. -/
theorem a3b4a_gysin_isolated_zero_local_trapping
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
    (f : C(E, E)) (r ρ : ℝ) (hρ : 0 < ρ)
    (hf : ∀ x ∈ Metric.closedBall (0 : E) r, f x = 0 → x = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∀ (t : unitInterval) (x : E), x ∈ Metric.closedBall (0 : E) r →
        a3b4a_gysin_translationHomotopy f a (t, x) = 0 →
          x ∈ Metric.ball (0 : E) ρ := by
  let K := Metric.closedBall (0 : E) r \ Metric.ball (0 : E) ρ
  have hK : IsCompact K := (isCompact_closedBall (0 : E) r).diff Metric.isOpen_ball
  have hnonzero : ∀ x ∈ K, f x ≠ 0 := by
    intro x hx hz
    have hx0 := hf x hx.1 hz
    exact hx.2 (hx0 ▸ Metric.mem_ball_self hρ)
  obtain ⟨ε, hε, hbound⟩ := a3b4a_gysin_compact_norm_lower_bound f K hK hnonzero
  refine ⟨ε, hε, ?_⟩
  intro a ha t x hxr hz
  by_contra hxρ
  have heq : f x = (t : ℝ) • a := sub_eq_zero.mp hz
  have ht : ‖(t : ℝ) • a‖ ≤ ‖a‖ := by
    rw [norm_smul, Real.norm_of_nonneg t.2.1]
    exact mul_le_of_le_one_left (norm_nonneg a) t.2.2
  exact (not_le_of_gt ha) ((hbound x ⟨hxr, hxρ⟩).trans (heq ▸ ht))

end HodgeLean.Adapters
