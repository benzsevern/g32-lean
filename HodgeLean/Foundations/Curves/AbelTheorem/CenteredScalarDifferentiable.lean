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

theorem mdifferentiable_of_centered_scalar (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (x : C) (hd : DifferentiableAt ℂ (centeredScalar h G x) 0) :
    MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) G x := by
  let L := b4cov_lineEquiv h
  let u : C → ℂ := fun y => L.symm (chartAt E x y - chartAt E x x)
  have hchart : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, E) (chartAt E x) x :=
    ((contMDiffOn_chart (I := 𝓘(ℂ, E)) (n := ω) (x := x)).contMDiffAt
      ((chartAt E x).open_source.mem_nhds (mem_chart_source E x))).mdifferentiableAt (by simp)
  have hu : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) u x :=
    L.symm.differentiableAt.mdifferentiableAt.comp x (hchart.sub mdifferentiableAt_const)
  have hux : u x = 0 := by simp only [u, sub_self, map_zero]
  have hd' : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (centeredScalar h G x) (u x) :=
    by rw [hux]; exact hd.mdifferentiableAt
  apply (hd'.comp x hu).congr_of_eventuallyEq
  filter_upwards [(chartAt E x).open_source.mem_nhds (mem_chart_source E x)] with y hy
  change G y = G ((chartAt E x).symm (chartAt E x x + L (L.symm (chartAt E x y - chartAt E x x))))
  rw [L.apply_symm_apply, add_sub_cancel, (chartAt E x).left_inv hy]

end HodgeLean.Foundations.Curves.AbelTheorem
