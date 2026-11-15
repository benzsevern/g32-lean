import HodgeLean.Foundations.Program.HolomorphicODEPicard
import HodgeLean.Foundations.Program.HolomorphicODEPrimitiveBounds

noncomputable section
open Set Metric Filter Topology
open scoped Interval
namespace HodgeLean.Foundations.Program

theorem b65_picardStep_dist_le {P E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup P] [NormedSpace ℂ P] [FiniteDimensional ℂ P]
    {A : P × (ℂ × E) → E} {c : ℂ} {y : E} {r S M d : ℝ} {U : Set P}
    (hS : 0 < S) (hM : 0 ≤ M) (hd : 0 ≤ d)
    (hA : AnalyticOnNhd ℂ A (U ×ˢ (ball c r ×ˢ ball y S)))
    (hb : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y S), ‖A q‖ ≤ M)
    {F G : P × (ℂ × E) → E}
    (hF : AnalyticOnNhd ℂ F (U ×ˢ (ball c r ×ˢ ball y (S / 2))))
    (hG : AnalyticOnNhd ℂ G (U ×ˢ (ball c r ×ˢ ball y (S / 2))))
    (hFm : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)), F q ∈ ball y (3 * S / 4))
    (hGm : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)), G q ∈ ball y (3 * S / 4))
    (hFG : ∀ q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)), ‖F q - G q‖ ≤ d)
    {q : P × (ℂ × E)} (hq : q ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2))) :
    ‖b65_picardStep A c F q - b65_picardStep A c G q‖ ≤ r * (4 * M / S) * d := by
  let : CompleteSpace E := FiniteDimensional.complete ℂ E
  have hs : ball y (3 * S / 4) ⊆ ball y S := ball_subset_ball (by linarith)
  have hFc := (b65_picardField_analytic hA hF (fun q hq ↦ hs (hFm q hq)) hq.1 hq.2.2).continuousOn
  have hGc := (b65_picardField_analytic hA hG (fun q hq ↦ hs (hGm q hq)) hq.1 hq.2.2).continuousOn
  have hdiff : ∀ x ∈ ball c r,
      ‖A (q.1, (x, F (q.1, (x, q.2.2)))) - A (q.1, (x, G (q.1, (x, q.2.2))))‖ ≤
        (4 * M / S) * d := by
    intro x hx
    have hm : (q.1, (x, q.2.2)) ∈ U ×ˢ (ball c r ×ˢ ball y (S / 2)) := ⟨hq.1, hx, hq.2.2⟩
    have ha : AnalyticOnNhd ℂ (fun v ↦ A (q.1, (x, v))) (ball y S) := by
      intro v hv
      apply (hA (q.1, (x, v)) ⟨hq.1, hx, hv⟩).comp (f := fun v : E ↦ (q.1, (x, v)))
      exact analyticAt_const.prod (analyticAt_const.prod analyticAt_id)
    exact (b65_state_lipschitz_bound hS hM ha
      (fun v hv ↦ hb (q.1, (x, v)) ⟨hq.1, hx, hv⟩) (hFm _ hm) (hGm _ hm)).trans
      (mul_le_mul_of_nonneg_left (hFG _ hm) (by positivity))
  simp only [b65_picardStep, add_sub_add_left_eq_sub]
  apply (b65_segmentPrimitive_dist_le hFc hGc hq.2.1 hdiff).trans
  calc
    ‖q.2.1 - c‖ * ((4 * M / S) * d) ≤ r * ((4 * M / S) * d) :=
      mul_le_mul_of_nonneg_right (mem_ball_iff_norm.mp hq.2.1).le (by positivity)
    _ = r * (4 * M / S) * d := by ring

end HodgeLean.Foundations.Program
