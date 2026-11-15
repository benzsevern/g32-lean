import HodgeLean.Foundations.Curves.AbelTheorem.Defs

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

theorem smooth_scalar_of_smooth_zero_form (f : C → ℝ)
    (hf : b3Forms_IsSmooth (b3Forms_fun (E := E) f)) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f := by
  intro x
  have hs := (b3Forms_isSmooth_fun_iff f).mp hf x
  have hc := (hs.contDiffAt ((chartAt E x).open_target.mem_nhds
    ((chartAt E x).map_source (mem_chart_source E x)))).contMDiffAt
  have hchart := (contMDiffOn_chart (I := 𝓘(ℝ, E)) (n := ∞) (x := x)).contMDiffAt
    ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))
  apply (hc.comp x hchart).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
  simp only [Function.comp_apply, (chartAt E x).left_inv hy]

end HodgeLean.Foundations.Curves.AbelTheorem
