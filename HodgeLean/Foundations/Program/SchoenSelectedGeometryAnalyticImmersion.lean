import HodgeLean.Foundations.Program.SchoenSelectedGeometryAnalyticEmbedding
import HodgeLean.Foundations.Program.SchoenSelectedGeometryUnramifiedInverse

noncomputable section
set_option maxHeartbeats 400000
open Set Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- An embedded holomorphic curve with locally unramified sphere coordinates has analytic image.
Source: Forster, Lectures on Riemann Surfaces, §2, and the local retraction criterion. -/
theorem s0_image_analytic_of_unramified_coordinates
    (n : ℕ) {C M : Type} [TopologicalSpace C] [ChartedSpace ℂ C]
    [IsManifold 𝓘(ℂ, ℂ) ω C] [TopologicalSpace M]
    [ChartedSpace (Fin n → ℂ) M] [IsManifold 𝓘(ℂ, Fin n → ℂ) ω M]
    (f : C → M) (hf : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, Fin n → ℂ) ω f)
    (he : IsClosedEmbedding f)
    (hq : ∀ x : C, ∃ q : M → OnePoint ℂ,
      ContMDiff 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω q ∧
        mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (q ∘ f) x ≠ 0) :
    IsClosedAnalytic (Fin n → ℂ) (range f) := by
  apply s0_image_analytic_of_local_left_inverses n f hf he.isClosed_range
  intro x
  obtain ⟨q, hqh, hqd⟩ := hq x
  obtain ⟨g, hg, _, hgf⟩ := s0_unramified_curve_local_inverse
    (q ∘ f) (hqh.comp hf) x hqd
  let k : M → C := g ∘ q
  have hk : ContMDiffAt 𝓘(ℂ, Fin n → ℂ) 𝓘(ℂ, ℂ) ω k (f x) :=
    hg.comp (f x) (hqh (f x))
  have hkN := (contMDiffAt_iff_contMDiffAt_nhds (by simp : (ω : ℕ∞ω) ≠ ∞)).mp hk
  have hleft : ∀ᶠ y in 𝓝 (f x), ∀ z, f z = y → k (f z) = z := by
    rw [he.isEmbedding.isInducing.nhds_eq_comap x] at hgf
    exact eventually_comap.mp hgf
  obtain ⟨V, hV, ho, hx⟩ := mem_nhds_iff.mp (hkN.and hleft)
  exact ⟨V, ho, hx, k, fun y hy ↦ (hV hy).1,
    fun z hz ↦ (hV hz).2 z rfl⟩

#print axioms s0_image_analytic_of_unramified_coordinates
end HodgeLean.Foundations.Program
