import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceChart
import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceOrbit

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The prescribed source rotation generator has a constructed logarithmic
lift whose full orbit returns by one positive primitive deck translation. -/
theorem s2v_l1b_action_rotgen_primitive_lift
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [Finite G] [MulAction G M]
    (x : M) (g : G) (hrot : b4_IsRotGen ℂ x g) :
    ∀ᶠ w : ℂ in comap Complex.re atBot,
      (s2v_l1b_action_sourceLift (s2v_l1b_action_sourceCoordinate x g)
        (2 * Real.pi * Complex.I / (orderOf g : ℂ)))^[orderOf g] w =
          w + 2 * Real.pi * Complex.I := by
  exact s2v_l1b_action_sourceLift_primitive_return
    (s2v_l1b_action_sourceCoordinate x g) _
    (s2v_l1b_action_sourceCoordinate_zero x g hrot.1)
    (s2v_l1b_action_sourceCoordinate_derivative x g hrot) (orderOf g) (orderOf_pos g)
    (by simp) (s2v_l1b_action_sourceCoordinate_period x g hrot)

end HodgeLean.Foundations.Program
