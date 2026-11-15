import HodgeLean.Foundations.Program.SchoenSelectedGeometryCurveInverse

noncomputable section
set_option maxHeartbeats 400000
open Set Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- An unramified holomorphic map of complex curves has a holomorphic local left inverse.
Source: Forster, Lectures on Riemann Surfaces, §2, via `b4cov_exists_localInverse`. -/
theorem s0_unramified_curve_local_inverse
    {C Y : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [TopologicalSpace Y] [ChartedSpace ℂ Y]
    [IsManifold 𝓘(ℂ, ℂ) ω Y]
    (f : C → Y) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω f)
    (x : C) (hd : mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) f x ≠ 0) :
    ∃ g : Y → C, ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω g (f x) ∧
      g (f x) = x ∧ ∀ᶠ z in 𝓝 x, g (f z) = z := by
  let φ := extChartAt 𝓘(ℂ, ℂ) x
  let ψ := extChartAt 𝓘(ℂ, ℂ) (f x)
  let G := b4cov_expr ℂ ℂ f x (f x)
  have hx : x ∈ φ.source := mem_extChartAt_source x
  have hy : f x ∈ ψ.source := mem_extChartAt_source (f x)
  have hGt : G (φ x) = ψ (f x) := by
    change ψ (f (φ.symm (φ x))) = ψ (f x)
    rw [φ.left_inv hx]
  have hG : AnalyticAt ℂ G (φ x) := b4cov_analyticAt_chart f hf x (f x)
    (φ x) (φ.map_source hx) (by rw [φ.left_inv hx]; exact hy)
  have hD : fderiv ℂ G (φ x) ≠ 0 :=
    (b4cov_mfderiv_ne_zero_iff_expr f hf x (f x) x hx hy).mp hd
  obtain ⟨σ, hσ, hσx, _, hσG⟩ := b4cov_exists_localInverse
    (Module.finrank_self ℂ) (Module.finrank_self ℂ) hG hD
  let g : Y → C := fun y ↦ φ.symm (σ (ψ y))
  have hs : σ (ψ (f x)) = φ x := by rw [← hGt]; exact hσx
  refine ⟨g, ?_, ?_, ?_⟩
  · have hi : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω φ.symm (φ x) :=
      (contMDiffOn_extChartAt_symm x).contMDiffAt
        ((isOpen_extChartAt_target x).mem_nhds (φ.map_source hx))
    have hσ' : ContMDiffAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω σ (ψ (f x)) := by
      rw [← hGt]
      exact hσ.contDiffAt.contMDiffAt
    exact (hi.comp_of_eq hσ' hs).comp (f x) contMDiffAt_extChartAt
  · change φ.symm (σ (ψ (f x))) = x
    rw [hs, φ.left_inv hx]
  · have hφ : ContinuousAt φ x := (contMDiffAt_extChartAt (n := ω)).continuousAt
    filter_upwards [(isOpen_extChartAt_source x).mem_nhds hx,
      hφ.tendsto.eventually hσG] with z hz hσz
    have he : G (φ z) = ψ (f z) := by
      change ψ (f (φ.symm (φ z))) = ψ (f z)
      rw [φ.left_inv hz]
    change φ.symm (σ (ψ (f z))) = z
    rw [← he, hσz, φ.left_inv hz]

#print axioms s0_unramified_curve_local_inverse
end HodgeLean.Foundations.Program
