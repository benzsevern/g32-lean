import HodgeLean.Foundations.Program.SchoenTowerL1bActionChartContinuity
import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceChart

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
namespace HodgeLean.Foundations.Program

/-- The actual source action is continuous because it is conjugate to the
continuous curve morphism. -/
theorem s2v_l1b_action_source_action_continuous
    (Y : Over (Spec ↧ℂ)) {M G : Type} [TopologicalSpace M]
    [Group G] [MulAction G M] (E : M ≃ₜ ComplexPoint Y) (f : Y ⟶ Y) (g : G)
    (hequiv : ∀ y, Point.map f (E y) = E (g • y)) :
    Continuous (fun y : M => g • y) := by
  have he : (fun y : M => g • y) = (fun y => E.symm (Point.map f (E y))) := by
    funext y
    rw [hequiv y, E.symm_apply_apply]
  rw [he]
  exact E.symm.continuous.comp ((Point.continuous_map f).comp E.continuous)

/-- The actual source-coordinate action is continuous at all points in a
sufficiently small neighbourhood of the fixed point. -/
theorem s2v_l1b_action_sourceCoordinate_eventually_continuousAt
    (Y : Over (Spec ↧ℂ)) {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [Group G] [MulAction G M] (E : M ≃ₜ ComplexPoint Y) (f : Y ⟶ Y) (g : G)
    (hequiv : ∀ y, Point.map f (E y) = E (g • y))
    (x : M) (hfix : g • x = x) :
    ∀ᶠ z : ℂ in 𝓝 0, ContinuousAt (s2v_l1b_action_sourceCoordinate x g) z := by
  let C := s2v_l1b_action_centerChart (chartAt ℂ x) x
  have hx : x ∈ C.source := by
    rw [s2v_l1b_action_centerChart_source]
    exact mem_chart_source ℂ x
  have hi := s2v_l1b_action_chart_eventually_continuousAt C x hx (fun y => g • y)
    (s2v_l1b_action_source_action_continuous Y E f g hequiv) hfix
  rw [show C x = 0 from s2v_l1b_action_centerChart_zero _ _] at hi
  exact hi

end HodgeLean.Foundations.Program
