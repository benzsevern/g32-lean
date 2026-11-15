import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.DiscCoefficientComparison

/-! # Normalized coordinates of the original curve discs -/
noncomputable section
set_option maxHeartbeats 400000
open Manifold Filter
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Program.G32Native
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]

/-- The original disc has its literal scalar parameter in the retained line coordinate. -/
theorem original_disc_normalized_coordinate (h : Module.finrank ℂ E = 1) (q : C) :
    (fun z : ℂ => (b4cov_lineEquiv h).symm
      (extChartAt 𝓘(ℂ, E) q (b3A_disc q (b4cov_lineEquiv h 1) z) -
        extChartAt 𝓘(ℂ, E) q q)) =ᶠ[𝓝 0] id := by
  let L := b4cov_lineEquiv h
  let e := chartAt E q
  have ht : ∀ᶠ z : ℂ in 𝓝 0, e q + z • L 1 ∈ e.target := by
    have hc : ContinuousAt (fun z : ℂ => e q + z • L 1) 0 := by fun_prop
    have heq : e q + (0 : ℂ) • L 1 = e q := by simp
    have hm : e q ∈ e.target := e.map_source (mem_chart_source E q)
    exact hc (by simpa only [heq] using e.open_target.mem_nhds hm)
  filter_upwards [ht] with z hz
  change L.symm (e (e.symm (e q + z • L 1)) - e q) = z
  rw [e.right_inv hz, add_sub_cancel_left]
  rw [← map_smul, smul_eq_mul, mul_one, L.symm_apply_apply]

/-- The original normalized disc passes through its marked point. -/
theorem original_disc_zero (h : Module.finrank ℂ E = 1) (q : C) :
    b3A_disc q (b4cov_lineEquiv h 1) 0 = q := by
  simp only [b3A_disc, zero_smul, add_zero]
  exact (chartAt E q).left_inv (mem_chart_source E q)

/-- The original normalized disc is continuous at its marked parameter. -/
theorem original_disc_continuousAt_zero (h : Module.finrank ℂ E = 1) (q : C) :
    ContinuousAt (b3A_disc q (b4cov_lineEquiv h 1)) 0 := by
  apply (b3A_disc_contMDiffAt q (b4cov_lineEquiv h 1) ?_).continuousAt
  simpa only [zero_smul, add_zero] using
    (chartAt E q).map_source (mem_chart_source E q)

#print axioms original_disc_normalized_coordinate
#print axioms original_disc_zero
#print axioms original_disc_continuousAt_zero
end HodgeLean.Foundations.Program.G32Native
