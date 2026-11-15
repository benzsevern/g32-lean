import HodgeLean.Foundations.Program.SchoenSelectedGeometryCenteredChart

noncomputable section
set_option maxHeartbeats 400000
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The centered chart expression has analytic order equal to the ramification index. -/
theorem s0_centeredChartMap_order
    {C Y : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [ConnectedSpace C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (hnc : ∃ x x', f x ≠ f x') (x : C) :
    analyticOrderAt (s0_centeredChartMap f x) 0 = b4_ramIndex ℂ ℂ f x := by
  obtain ⟨hp, hn, hl⟩ := b4cov_ramIndex_spec f hf hnc x
  exact b4cov_analyticOrderAt_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ)
    (b4cov_analyticOnNhd f hf x _ (b4cov_mem_good f x)) hp hl hn

#print axioms s0_centeredChartMap_order
end HodgeLean.Foundations.Program
