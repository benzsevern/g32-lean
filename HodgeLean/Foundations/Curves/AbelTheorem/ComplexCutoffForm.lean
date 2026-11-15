import HodgeLean.Foundations.Curves.AbelTheorem.ComplexMultiplierRegularity

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]
attribute [local instance] b3Forms_isManifold_real

theorem complex_cutoff_coefficient_smooth (h : Module.finrank ℂ E = 1)
    (w : b4c_MeroForm E C h) (μ : C → ℝ)
    (hμ : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ μ)
    (hpoles : ∀ x, meromorphicOrderAt (HurwitzPrymRR_loc h w x) 0 < 0 → μ =ᶠ[𝓝 x] 0)
    (G : C → ℂ) (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G) (x : C) :
    ContDiffAt ℝ ∞ (HurwitzPrymRR_loc h
      (fun v => G v.proj * ((μ v.proj : ℂ) * b4c_residue_normalizedForm h w v)) x) 0 := by
  change ContDiffAt ℝ ∞ (fun z => centeredScalar h G x z *
    HurwitzPrymRR_loc h (fun v => (μ v.proj : ℂ) * b4c_residue_normalizedForm h w v) x z) 0
  exact (centered_smooth_scalar h G hG x).mul
    (b4c_residue_cutoff_coefficient_smooth h w μ hμ hpoles x)

end HodgeLean.Foundations.Curves.AbelTheorem
