import HodgeLean.Foundations.Program.SchoenSelectedGeometryTransportComposition

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- Centered expressions of curve maps respect composition as analytic germs. -/
theorem s0_centeredChartMap_comp
    {C Y Z : Type}
    [TopologicalSpace C] [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C]
    [TopologicalSpace Y] [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ, ℂ) ω Y]
    [TopologicalSpace Z] [ChartedSpace ℂ Z] [IsManifold 𝓘(ℂ, ℂ) ω Z]
    (f : C → Y) (g : Y → Z) (hf : Continuous f) (x : C) :
    s0_centeredChartMap (g ∘ f) x =ᶠ[𝓝 (0 : ℂ)]
      (s0_centeredChartMap g (f x)) ∘ (s0_centeredChartMap f x) := by
  let φ := extChartAt 𝓘(ℂ, ℂ) x
  let ψ := extChartAt 𝓘(ℂ, ℂ) (f x)
  let χ := extChartAt 𝓘(ℂ, ℂ) (g (f x))
  let F := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x f
  let G := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (f x) g
  let FG := writtenInExtChartAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) x (g ∘ f)
  have he : FG =ᶠ[𝓝 (φ x)] G ∘ F := by
    filter_upwards [b4cov_good_nhds (E := ℂ) (E' := ℂ) f hf x] with z hz
    change χ (g (f (φ.symm z))) = χ (g (ψ.symm (ψ (f (φ.symm z)))))
    rw [ψ.left_inv hz.2]
  let L := b4cov_lineEquiv (Module.finrank_self ℂ)
  have hshift : Continuous (fun z : ℂ ↦ φ x + L z) := continuous_const.add L.continuous
  have ht : Tendsto (fun z : ℂ ↦ φ x + L z) (𝓝 0) (𝓝 (φ x)) := by
    simpa only [map_zero, add_zero] using (hshift.continuousAt (x := (0 : ℂ))).tendsto
  have het := he.comp_tendsto ht
  have htr : b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ) FG (φ x) =ᶠ[𝓝 (0 : ℂ)]
      b4cov_transport (Module.finrank_self ℂ) (Module.finrank_self ℂ) (G ∘ F) (φ x) := by
    filter_upwards [het] with z hz
    change L.symm (FG (φ x + L z)) - L.symm (FG (φ x)) =
      L.symm ((G ∘ F) (φ x + L z)) - L.symm ((G ∘ F) (φ x))
    simp only [Function.comp_apply] at hz
    rw [hz, he.self_of_nhds]
    rfl
  have hF : F (φ x) = ψ (f x) := by
    simp only [F, φ, ψ, writtenInExtChartAt, Function.comp_apply, extChartAt_to_inv]
  have hc := s0_transport_comp F G (φ x)
  rw [hF] at hc
  exact htr.trans (Filter.EventuallyEq.of_eq hc)

#print axioms s0_centeredChartMap_comp
end HodgeLean.Foundations.Program
