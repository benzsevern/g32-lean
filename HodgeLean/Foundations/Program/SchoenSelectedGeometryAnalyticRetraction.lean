import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticImage

noncomputable section
set_option maxHeartbeats 400000
open Set Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- Local holomorphic retractions exhibit a subset as an analytic set.
Source: local equations obtained by subtracting the retraction from the identity in a chart. -/
theorem s0_closedAnalytic_of_local_retractions
    (n : ℕ) {M : Type} [TopologicalSpace M] [ChartedSpace (Fin n → ℂ) M]
    [IsManifold 𝓘(ℂ, Fin n → ℂ) ω M]
    (Z : Set M) (hc : IsClosed Z)
    (hl : ∀ p ∈ Z, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∃ r : M → M,
      (∀ y ∈ U, ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω r y) ∧
      ∀ y ∈ U, y ∈ Z ↔ r y = y) :
    IsClosedAnalytic (Fin n → ℂ) Z := by
  apply s0_closedAnalytic_of_local_scalar_equations Z hc
  intro p hp
  obtain ⟨U, ho, hU, r, hr, hz⟩ := hl p hp
  let φ := chartAt (Fin n → ℂ) p
  have hpφ : p ∈ φ.source := mem_chart_source _ p
  have hrp : r p = p := (hz p hU).mp hp
  have hn : U ∩ φ.source ∩ r ⁻¹' φ.source ∈ 𝓝 p := by
    refine inter_mem (inter_mem (ho.mem_nhds hU) (φ.open_source.mem_nhds hpφ)) ?_
    exact (hr p hU).continuousAt (φ.open_source.mem_nhds (by rw [hrp]; exact hpφ))
  obtain ⟨V, hV, hVo, hpV⟩ := mem_nhds_iff.mp hn
  refine ⟨V, hVo, hpV, n, fun i y ↦ φ (r y) i - φ y i, ?_, ?_⟩
  · intro i y hy
    have h := hV hy
    have h₁ : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω φ (r y) :=
      contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas p) h.2
    have h₂ : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, Fin n → ℂ) ω φ y :=
      contMDiffAt_of_mem_maximalAtlas
      (IsManifold.chart_mem_maximalAtlas p) h.1.2
    have hπ : ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω (fun v : Fin n → ℂ ↦ v i) :=
      (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ↦ ℂ) i).contDiff.contMDiff
    exact ((hπ.contMDiffAt.comp (r y) h₁).comp y (hr y h.1.1)).sub
      (hπ.contMDiffAt.comp y h₂)
  · intro y hy
    have h := hV hy
    rw [hz y h.1.1]
    simp only [sub_eq_zero]
    constructor
    · intro he i
      rw [he]
    · intro he
      exact φ.injOn h.2 h.1.2 (funext he)

#print axioms s0_closedAnalytic_of_local_retractions
end HodgeLean.Foundations.Program
