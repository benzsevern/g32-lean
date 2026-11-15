import HodgeLean.Foundations.Program.SchoenTowerL1bActionNativeCoordinateAction
import HodgeLean.Foundations.Program.SchoenTowerL1bActionSourceChart

noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program

/-- The actual centered native representative intertwines the source
generator and the native action on a neighbourhood of zero. -/
theorem s2v_l1b_action_nativeConjugacy_intertwines
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [MulAction G M]
    (E : M ≃ₜ ComplexPoint Y) (f : Y ⟶ Y) (g : G)
    (hequiv : ∀ y, Point.map f (E y) = E (g • y))
    (x : M) (hrot : b4_IsRotGen ℂ x g) :
    let D := s2v_l1b_action_centerChart (s2v_l1b_action_nativePlaneChart Y (E x)) (E x)
    ∀ᶠ z : ℂ in 𝓝 0,
      s2v_l1b_action_nativeConjugacy Y E x (s2v_l1b_action_sourceCoordinate x g z) =
        D (Point.map f (D.symm (s2v_l1b_action_nativeConjugacy Y E x z))) := by
  let C := s2v_l1b_action_centerChart (chartAt ℂ x) x
  let D := s2v_l1b_action_centerChart (s2v_l1b_action_nativePlaneChart Y (E x)) (E x)
  have hx : x ∈ C.source := by
    rw [s2v_l1b_action_centerChart_source]
    exact mem_chart_source ℂ x
  have hy : E x ∈ D.source := by
    rw [s2v_l1b_action_centerChart_source]
    exact s2v_l1b_action_nativePlaneChart_source Y (E x)
  have hi := s2v_l1b_action_chart_conjugacy_eventually C D E x hx hy
    (fun y => g • y) (Point.map f)
    (s2v_l1b_action_rotgen_mdifferentiableAt x g hrot).continuousAt hrot.1 hequiv
  rw [show C x = 0 from s2v_l1b_action_centerChart_zero _ _] at hi
  exact hi

/-- The centered homeomorphism intertwines the preferred source-coordinate
action with the precise native function in the derivative statement. -/
theorem s2v_l1b_action_nativeConjugacy_intertwines_coordinate
    (Y : Over (Spec ↧ℂ)) [SmoothOfRelativeDimension 1 Y.hom]
    {M G : Type} [TopologicalSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ, ℂ) ω M] [Group G] [MulAction G M]
    (E : M ≃ₜ ComplexPoint Y) (f : Y ⟶ Y) (g : G)
    (hequiv : ∀ y, Point.map f (E y) = E (g • y))
    (x : M) (hrot : b4_IsRotGen ℂ x g) :
    ∀ᶠ z : ℂ in 𝓝 0,
      s2v_l1b_action_nativeConjugacy Y E x (s2v_l1b_action_sourceCoordinate x g z) =
        ComplexPoint.localChart Y 1 (E x)
          (Point.map f (s2e_u1_nativeCurve Y (E x)
            (s2v_l1b_action_nativeConjugacy Y E x z))) 0 -
              ComplexPoint.localChart Y 1 (E x) (E x) 0 := by
  have hi := s2v_l1b_action_nativeConjugacy_intertwines Y E f g hequiv x hrot
  filter_upwards [hi] with z hz
  exact hz.trans (s2v_l1b_action_centered_native_action Y (E x) f _)

end HodgeLean.Foundations.Program
