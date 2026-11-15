import HodgeLean.Foundations.Program.HolomorphicODEPrimitive

noncomputable section
open Set Metric Filter Topology
open scoped Interval
namespace HodgeLean.Foundations.Program

theorem b65_segmentPrimitive_dist_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [CompleteSpace E] {f g : ℂ → E} {c x : ℂ} {r d : ℝ}
    (hf : ContinuousOn f (ball c r)) (hg : ContinuousOn g (ball c r))
    (hx : x ∈ ball c r) (hb : ∀ v ∈ ball c r, ‖f v - g v‖ ≤ d) :
    ‖b65_segmentPrimitive f c x - b65_segmentPrimitive g c x‖ ≤ ‖x - c‖ * d := by
  have hcont (h : ℂ → E) (hh : ContinuousOn h (ball c r)) :
      ContinuousOn (fun t : ℝ ↦ h (c + (t : ℂ) * (x - c))) (uIcc (0 : ℝ) 1) := by
    apply hh.comp (show Continuous (fun t : ℝ ↦ c + (t : ℂ) * (x - c)) from by fun_prop).continuousOn
    intro t ht
    exact b65_segment_mem_ball hx (by simpa using ht)
  have heq : b65_segmentPrimitive f c x - b65_segmentPrimitive g c x =
      b65_segmentPrimitive (fun v ↦ f v - g v) c x := by
    simp only [b65_segmentPrimitive]
    rw [← smul_sub, intervalIntegral.integral_sub (hcont f hf).intervalIntegrable
      (hcont g hg).intervalIntegrable]
  rw [heq]
  exact b65_segmentPrimitive_norm_le hx hb

end HodgeLean.Foundations.Program
