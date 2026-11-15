import HodgeLean.Foundations.Curves.AbelTheorem.CenteredScalarDifferentiable

noncomputable section
open HodgeLean.Foundations.Program
open Set Filter Manifold
open scoped Topology ContDiff
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {E C : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [FiniteDimensional ℂ E] [TopologicalSpace C] [ChartedSpace E C]
  [IsManifold 𝓘(ℂ, E) ω C]

/-- Source: Forster, Lectures on Riemann Surfaces, §2, holomorphic coordinate invariance. -/
theorem centered_scalar_differentiable_of_mdifferentiable (h : Module.finrank ℂ E = 1)
    (G : C → ℂ) (x : C) (z : ℂ)
    (hz : chartAt E x x + b4cov_lineEquiv h z ∈ (chartAt E x).target)
    (hG : MDifferentiableAt 𝓘(ℂ, E) 𝓘(ℂ, ℂ) G
      ((chartAt E x).symm (chartAt E x x + b4cov_lineEquiv h z))) :
    DifferentiableAt ℂ (centeredScalar h G x) z := by
  have hi := ((contMDiffOn_chart_symm (I := 𝓘(ℂ, E)) (n := ω) (x := x)).contMDiffAt
    ((chartAt E x).open_target.mem_nhds hz)).mdifferentiableAt (by simp)
  have ha : MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, E)
      (fun u : ℂ => chartAt E x x + b4cov_lineEquiv h u) z :=
    ((b4cov_lineEquiv h).differentiableAt.const_add _).mdifferentiableAt
  exact (hG.comp z (hi.comp z ha)).differentiableAt

end HodgeLean.Foundations.Curves.AbelTheorem
