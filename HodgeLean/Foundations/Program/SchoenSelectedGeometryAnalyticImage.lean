import HodgeLean.Foundations.AnalyticSubset
import HodgeLean.Foundations.Program.SchoenSelectedGeometryCurveInverse

noncomputable section
set_option maxHeartbeats 400000
open Set Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Local holomorphic scalar equations give the chart equations of an analytic subset.
Source: the local defining-equation characterization of complex analytic subsets. -/
theorem s0_closedAnalytic_of_local_scalar_equations
    {E M : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ω M]
    (Z : Set M) (hc : IsClosed Z)
    (hl : ∀ p ∈ Z, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∃ (n : ℕ) (f : Fin n → M → ℂ),
        (∀ i y, y ∈ U → ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) ω (f i) y) ∧
        ∀ y ∈ U, y ∈ Z ↔ ∀ i, f i y = 0) :
    IsClosedAnalytic E Z := by
  refine ⟨hc, ?_⟩
  intro p hp
  obtain ⟨U, ho, hU, n, f, hf, hz⟩ := hl p hp
  let φ := chartAt E p
  have hφ : p ∈ φ.source := mem_chart_source E p
  refine ⟨φ.target ∩ φ.symm ⁻¹' U, φ.isOpen_inter_preimage_symm ho,
    ⟨φ.map_source hφ, ?_⟩, inter_subset_left, n,
    fun i v ↦ f i (φ.symm v), ?_, ?_⟩
  · change φ.symm (φ p) ∈ U
    rw [φ.left_inv hφ]
    exact hU
  · intro i v hv
    have h : ContMDiffAt 𝓘(ℂ, E) 𝓘(ℂ, E) ω φ.symm v :=
      contMDiffAt_symm_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas p) hv.1
    exact ((hf i _ hv.2).comp v h).contDiffAt.analyticAt
  · intro v hv
    exact hz _ hv.2

#print axioms s0_closedAnalytic_of_local_scalar_equations
end HodgeLean.Foundations.Program
