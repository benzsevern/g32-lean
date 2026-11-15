import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticImage

noncomputable section
set_option maxHeartbeats 400000
open Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Holomorphic preimages of analytic subsets are analytic.
Source: composition of local analytic defining equations with holomorphic maps. -/
theorem s0_closedAnalytic_preimage
    {E E' M M' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup E'] [NormedSpace ℂ E']
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    [TopologicalSpace M'] [ChartedSpace E' M'] [IsManifold 𝓘(ℂ, E') ω M']
    (f : M → M') (hf : ContMDiff 𝓘(ℂ, E) 𝓘(ℂ, E') ω f)
    (Z : Set M') (hZ : IsClosedAnalytic E' Z) : IsClosedAnalytic E (f ⁻¹' Z) := by
  apply s0_closedAnalytic_of_local_scalar_equations _ (hZ.1.preimage hf.continuous)
  intro p hp
  obtain ⟨U, ho, hU, htarget, n, g, hg, hz⟩ := hZ.2 (f p) hp
  let ψ := chartAt E' (f p)
  let V := f ⁻¹' (ψ.source ∩ ψ ⁻¹' U)
  have hpψ : f p ∈ ψ.source := mem_chart_source _ _
  refine ⟨V, (ψ.isOpen_inter_preimage ho).preimage hf.continuous,
    ⟨hpψ, hU⟩, n, fun i x ↦ g i (ψ (f x)), ?_, ?_⟩
  · intro i y hy
    have hc : ContMDiffAt 𝓘(ℂ, E') 𝓘(ℂ, E') ω ψ (f y) :=
      contMDiffAt_of_mem_maximalAtlas (IsManifold.chart_mem_maximalAtlas (f p)) hy.1
    exact ((hg i _ hy.2).contDiffAt.contMDiffAt.comp (f y) hc).comp y (hf y)
  · intro y hy
    have h := hz (ψ (f y)) hy.2
    rw [ψ.left_inv hy.1] at h
    exact h

#print axioms s0_closedAnalytic_preimage
end HodgeLean.Foundations.Program
