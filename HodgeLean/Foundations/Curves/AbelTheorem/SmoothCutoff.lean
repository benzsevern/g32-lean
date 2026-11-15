import HodgeLean.Foundations.Curves.AbelTheorem.Defs

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C] [T2Space C] [CompactSpace C]
attribute [local instance] b3Forms_isManifold_real

theorem smooth_cutoff_of_disjoint_closed (S A : Set C) (hS : IsClosed S)
    (hA : IsClosed A) (hd : Disjoint S A) :
    ∃ μ : C → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ μ ∧
      (∀ x ∈ S, μ =ᶠ[𝓝 x] 0) ∧ (∀ x ∈ A, μ =ᶠ[𝓝 x] fun _ => 1) := by
  obtain ⟨μ, hzero, hone, _⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed
    𝓘(ℝ, E) (n := (⊤ : ℕ∞)) hS hA hd
  refine ⟨μ, μ.contMDiff, ?_, ?_⟩
  · intro x hx
    filter_upwards [hzero.filter_mono (nhds_le_nhdsSet hx)] with y hy
    exact hy
  · intro x hx
    exact hone.filter_mono (nhds_le_nhdsSet hx)

end HodgeLean.Foundations.Curves.AbelTheorem
