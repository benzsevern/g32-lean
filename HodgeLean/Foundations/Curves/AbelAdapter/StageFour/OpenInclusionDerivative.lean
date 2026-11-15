import HodgeLean.Foundations.Program.RiemannRoch

noncomputable section
open HodgeLean.Foundations.Program
open Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Curves.AbelAdapter.StageFour

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Source: Forster, Lectures on Riemann Surfaces, §2, the tangent map of an open inclusion. -/
theorem openInclusion_mfderiv
    {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace C] [ChartedSpace E C] [IsManifold 𝓘(ℂ, E) ω C]
    (U : TopologicalSpace.Opens C) (x : U) :
    mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : U => (y : C)) x = ContinuousLinearMap.id ℂ E := by
  have hv := (contMDiff_subtype_val (I := 𝓘(ℂ, E)) (n := ω) x).mdifferentiableAt (by simp)
  have hc := (contMDiffAt_extChartAt (I := 𝓘(ℂ, E)) (n := ω) (x := (x : C))).mdifferentiableAt
    (by simp)
  have he : (extChartAt 𝓘(ℂ, E) (x : C)) ∘ (fun y : U => (y : C)) =
      extChartAt 𝓘(ℂ, E) x := rfl
  have hm := mfderiv_comp x hc hv
  rw [he, mfderiv_extChartAt_self, mfderiv_extChartAt_self] at hm
  change ContinuousLinearMap.id ℂ E = (ContinuousLinearMap.id ℂ E).comp
    (mfderiv 𝓘(ℂ, E) 𝓘(ℂ, E) (fun y : U => (y : C)) x) at hm
  simpa only [ContinuousLinearMap.id_comp] using hm.symm

end HodgeLean.Foundations.Curves.AbelAdapter.StageFour
