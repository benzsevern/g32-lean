import HodgeLean.Foundations.Curves.AbelAdapter.StageFour.OpenInclusionDerivative

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Forster, Lectures on Riemann Surfaces, §§2, 9, compatibility of open restriction and local coefficients. -/
theorem openRestriction_local_coefficient
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (h : Module.finrank ℂ E = 1) (U : TopologicalSpace.Opens C)
    (θ : TangentBundle 𝓘(ℂ, E) C → ℂ) (hθ : HurwitzPrymRR_IsLinear θ) (x : U) :
    HurwitzPrymRR_loc h (b3_pullback E E (fun y : U => (y : C)) θ) x =ᶠ[𝓝 0]
      HurwitzPrymRR_loc h θ (x : C) := by
  let c := extChartAt 𝓘(ℂ, E) x x
  let L := b4cov_lineEquiv h
  let g := b4cov_expr E E (fun y : U => (y : C)) x (x : C)
  have hg : g =ᶠ[𝓝 c] id := by
    filter_upwards [(isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)] with t ht
    change (extChartAt 𝓘(ℂ, E) x) ((extChartAt 𝓘(ℂ, E) x).symm t) = t
    exact (extChartAt 𝓘(ℂ, E) x).right_inv ht
  have hmap : Tendsto (fun t : ℂ => c + L t) (𝓝 0) (𝓝 c) := by
    have hcont : Continuous (fun t : ℂ => c + L t) := continuous_const.add L.continuous
    simpa only [map_zero, add_zero] using (hcont.continuousAt (x := 0)).tendsto
  let T := b4cov_transport h h g c
  have hT : T =ᶠ[𝓝 0] id := by
    filter_upwards [hmap hg] with t ht
    change L.symm (g (c + L t)) - L.symm (g c) = t
    rw [ht, hg.eq_of_nhds, ← map_sub]
    simp only [id_eq, add_sub_cancel_left, ContinuousLinearEquiv.symm_apply_apply]
  have he := HurwitzPrymRR_loc_pullback h h (fun y : U => (y : C))
    contMDiff_subtype_val x (x : C) (mem_extChartAt_source (x : C)) θ hθ
  filter_upwards [he, hT, hT.deriv] with t ht htT htD
  simp only [sub_self, map_zero, zero_add] at ht
  change HurwitzPrymRR_loc h (b3_pullback E E (fun y : U => (y : C)) θ) x t =
    HurwitzPrymRR_loc h θ (x : C) (T t) * deriv T t at ht
  rw [ht, htT, htD]
  simp

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
