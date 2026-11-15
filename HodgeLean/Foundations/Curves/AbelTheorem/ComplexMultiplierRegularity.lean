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

theorem centered_smooth_scalar (h : Module.finrank ℂ E = 1) (G : C → ℂ)
    (hG : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞ G) (x : C) :
    ContDiffAt ℝ ∞ (centeredScalar h G x) 0 := by
  let A : ℂ → E := fun z => chartAt E x x + b4cov_lineEquiv h z
  have hA : ContDiffAt ℝ ∞ A 0 :=
    contDiffAt_const.add ((b4cov_lineEquiv h).contDiff.restrict_scalars ℝ).contDiffAt
  have hA0 : A 0 = chartAt E x x := by simp only [A, map_zero, add_zero]
  have hchart : ContDiffAt ℝ ∞ (G ∘ (chartAt E x).symm) (A 0) := by
    rw [hA0]
    exact (hG.comp_contMDiffOn (contMDiffOn_chart_symm (I := 𝓘(ℝ, E)) (x := x))).contDiffOn.contDiffAt
      ((chartAt E x).open_target.mem_nhds ((chartAt E x).map_source (mem_chart_source E x)))
  exact hchart.comp 0 hA

end HodgeLean.Foundations.Curves.AbelTheorem
