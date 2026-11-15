import HodgeLean.Foundations.Program.HurwitzPrymCovDegree

noncomputable section
set_option maxHeartbeats 400000
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The expression of a curve map in normalized charts centered at the source and image points. -/
def s0_centeredChartMap
    {C Y : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] (f : C → Y) (x : C) : ℂ → ℂ :=
  b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ)
    (writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f) (extChartAt 𝓘(ℂ, ℂ) x x)

/-- The centered chart expression of a holomorphic curve map is analytic at zero. -/
theorem s0_centeredChartMap_analytic
    {C Y : Type} [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f) (x : C) :
    AnalyticAt ℂ (s0_centeredChartMap f x) 0 :=
  b4cov_transport_analyticAt (Module.finrank_self ℂ) (Module.finrank_self ℂ)
    (b4cov_analyticOnNhd f hf x _ (b4cov_mem_good f x))

#print axioms s0_centeredChartMap_analytic
end HodgeLean.Foundations.Program
