import HodgeLean.Foundations.Program.SchoenTowerL1bActionSplitDefs

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Manifold
open scoped ContDiff
namespace HodgeLean.Foundations.Program

/-- The specified rotation generator is differentiable at its fixed point;
its prescribed differential is injective because its scalar is nonzero. -/
theorem s2v_l1b_action_rotgen_mdifferentiableAt
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [MulAction G M]
    (x : M) (g : G) (hrot : b4_IsRotGen ℂ x g) :
    MDifferentiableAt 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) (fun y : M => g • y) x := by
  apply mdifferentiableAt_of_mfderiv_injective
  intro v w hvw
  rw [hrot.2.2, hrot.2.2] at hvw
  exact smul_right_injective _ (Complex.exp_ne_zero _) hvw

end HodgeLean.Foundations.Program
