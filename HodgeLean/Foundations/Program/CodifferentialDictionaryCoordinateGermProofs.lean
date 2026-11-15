import HodgeLean.Foundations.Program.CodifferentialDictionaryRamificationIndexProofs

noncomputable section
open Filter Topology
namespace HodgeLean.Foundations.Program

theorem b66d_eventuallyEq_of_coordinate_comp (F f g : ℂ → ℂ) (α : ℂ)
    (hF : AnalyticAt ℂ F α) (hF0 : F α = 0) (hFd : deriv F α ≠ 0)
    (h : (f ∘ F) =ᶠ[𝓝[≠] α] (g ∘ F)) : f =ᶠ[𝓝[≠] 0] g := by
  have hmap := hF.hasStrictDerivAt.map_nhds_eq hFd
  rw [hF0] at hmap
  have hnear : ∀ᶠ z in 𝓝 α, F z ≠ 0 → f (F z) = g (F z) := by
    change ∀ᶠ z in 𝓝[≠] α, f (F z) = g (F z) at h
    rw [eventually_nhdsWithin_iff] at h
    filter_upwards [h] with z hz hne
    apply hz
    intro he
    exact hne (he ▸ hF0)
  have hzero : ∀ᶠ w in 𝓝 (0 : ℂ), w ≠ 0 → f w = g w := by
    rw [← hmap]
    exact hnear
  change ∀ᶠ w in 𝓝[≠] (0 : ℂ), f w = g w
  rw [eventually_nhdsWithin_iff]
  exact hzero

end HodgeLean.Foundations.Program
