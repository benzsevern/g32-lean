import HodgeLean.Foundations.Program.SchoenTowerL1bActionRotationDerivative
import Mathlib.Analysis.Calculus.Deriv.Slope
import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartPeriod

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Manifold Filter
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The rotation generator has its prescribed scalar as the actual complex
derivative in the preferred source chart. -/
theorem s2v_l1b_action_rotgen_chart_derivative
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [MulAction G M]
    (x : M) (g : G) (hrot : b4_IsRotGen ℂ x g) :
    HasDerivAt (fun z : ℂ => chartAt ℂ x (g • (chartAt ℂ x).symm z))
      (Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ))) (chartAt ℂ x x) := by
  have h := (s2v_l1b_action_rotgen_mdifferentiableAt x g hrot).hasMFDerivAt.2
  simp only [modelWithCornersSelf_coe, Set.range_id, hasFDerivWithinAt_univ] at h
  apply hasDerivAt_iff_hasFDerivAt.mpr
  convert h using 1
  · funext z
    simp only [writtenInExtChartAt, extChartAt_coe, extChartAt_coe_symm,
      modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm, Function.comp_apply, hrot.1, id_eq]
  · apply ContinuousLinearMap.ext
    intro v
    change v * Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ)) =
      (mfderiv 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y : M => g • y) x v : ℂ)
    rw [hrot.2.2]
    exact mul_comm _ _
  · simp only [extChartAt_coe, modelWithCornersSelf_coe, Function.comp_apply, id_eq]

/-- The source action in its preferred chart, centered at the rotation point. -/
def s2v_l1b_action_sourceCoordinate
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [Group G] [MulAction G M]
    (x : M) (g : G) (z : ℂ) : ℂ :=
  chartAt ℂ x (g • (chartAt ℂ x).symm (z + chartAt ℂ x x)) - chartAt ℂ x x

/-- The centered source-coordinate action fixes zero. -/
theorem s2v_l1b_action_sourceCoordinate_zero
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M] [Group G] [MulAction G M]
    (x : M) (g : G) (hfix : g • x = x) :
    s2v_l1b_action_sourceCoordinate x g 0 = 0 := by
  simp only [s2v_l1b_action_sourceCoordinate, zero_add,
    (chartAt ℂ x).left_inv (mem_chart_source ℂ x), hfix, sub_self]

/-- Centering the source chart retains the prescribed rotation derivative. -/
theorem s2v_l1b_action_sourceCoordinate_derivative
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [MulAction G M]
    (x : M) (g : G) (hrot : b4_IsRotGen ℂ x g) :
    HasDerivAt (s2v_l1b_action_sourceCoordinate x g)
      (Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ))) 0 := by
  let c := chartAt ℂ x x
  have hraw := s2v_l1b_action_rotgen_chart_derivative x g hrot
  have ho : HasDerivAt (fun z : ℂ => chartAt ℂ x (g • (chartAt ℂ x).symm z))
      (Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ)))
      ((fun z : ℂ => z + c) 0) := by
    simpa only [zero_add, c] using hraw
  have hh := (ho.comp (0 : ℂ) ((hasDerivAt_id (0 : ℂ)).add_const c)).sub_const c
  change HasDerivAt (fun z : ℂ => chartAt ℂ x
    (g • (chartAt ℂ x).symm (z + c)) - c)
    (Complex.exp (2 * Real.pi * Complex.I / (orderOf g : ℂ))) 0
  convert hh using 1 <;> first | rfl | exact (mul_one _).symm

/-- The actual source group period is a local period of the centered
source-coordinate action. -/
theorem s2v_l1b_action_sourceCoordinate_period
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [MulAction G M]
    (x : M) (g : G) (hrot : b4_IsRotGen ℂ x g) :
    ∀ᶠ z : ℂ in nhds 0, (s2v_l1b_action_sourceCoordinate x g)^[orderOf g] z = z := by
  have hp (y : M) : (fun y : M => g • y)^[orderOf g] y = y := by
    rw [smul_iterate_apply, pow_orderOf_eq_one, one_smul]
  exact s2v_l1b_action_centered_chart_period_eventually (chartAt ℂ x) x
    (mem_chart_source ℂ x) (fun y : M => g • y)
    (s2v_l1b_action_rotgen_mdifferentiableAt x g hrot).continuousAt hrot.1 (orderOf g) hp

end HodgeLean.Foundations.Program
