import HodgeLean.Foundations.Program.RelativeFrameFamilyPowerChart

noncomputable section
open Set Metric Manifold Filter Topology
open scoped ContDiff
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

/-- The outer boundary stays outside every tent support.
Source: `rf7_outer_closure`, `b6t_discs`. -/
theorem rf7_outer_closure_stationary {b : Fin 10 → ℂ} {C : Type} [TopologicalSpace C]
    (hb : b ∈ b6_chart) (f : C → OnePoint ℂ) (hf : Continuous f) :
    closure (rf7_outer b f) ⊆ f ⁻¹' b6a_stationaryOpen b := by
  intro y hy
  have hρ : b6t_radius b < rf7_radius b := by
    have hr := (b6t_discs b hb).1
    unfold rf7_radius
    linarith
  have hh := rf7_outer_closure f hf hy
  intro h
  obtain ⟨i, z, hz, he⟩ := mem_iUnion.mp h
  apply hh i
  exact ⟨z, lt_of_le_of_lt hz hρ, he⟩

end HodgeLean.Foundations.Program
