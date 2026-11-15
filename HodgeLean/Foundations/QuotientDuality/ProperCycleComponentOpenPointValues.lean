import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentOpenSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSupportPointValues
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenHolomorphicChart
import HodgeLean.Foundations.QuotientDuality.ProperCycleSmoothHolomorphicChart

/-! # Nonzero intrinsic point values throughout selected smooth component opens
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
open TopologicalSpace HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified intrinsic component class has nonzero original local value at every point of an actual isolated affine smooth component open.
Source: properCycle_holomorphic_vector_chart_open_transport; properCycle_intrinsic_support_component_point_ne_zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_component_open_point_ne_zero
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ))
    (W : (properCycle_component_over X ξ).left.Opens) (hW : IsAffineOpen W)
    [SmoothOfRelativeDimension d (openScheme (properCycle_component_over X ξ) W).hom]
    (hother : ∀ z : (properCycle_component_over X ξ).left, z ∈ W →
      ∀ η ∈ γ.support, η ≠ ξ →
        (properCycle_component_over_inclusion X ξ).left z ∉ closure ({η} : Set X.left))
    (y : ComplexPoint (openScheme (properCycle_component_over X ξ) W)) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)
      (properCycle_intrinsic_component_on_support X γ ξ hξ d hdim)
      (properCycle_component_open_support_map X γ ξ hξ W y) ≠ 0 := by
  let V := properCycle_component_over X ξ
  let Y := openScheme V W
  letI : IsAffine Y.left := hW
  letI : QuasiCompact Y.hom := inferInstance
  letI : IsSeparated Y.hom := inferInstance
  letI : Nonempty (ComplexPoint Y) := ⟨y⟩
  letI : Smooth Y.hom := SmoothOfRelativeDimension.smooth d Y.hom
  obtain ⟨e, he, hsource, _⟩ := properCycle_holomorphic_vector_chart_open_transport V W d
    (localChart Y d y) (properCycle_smooth_local_chart_holomorphic Y d y)
  let u := Point.map (openInclusion V W) y
  have hu : u ∈ e.source := by
    rw [hsource]
    exact ⟨y, mem_localChart_source Y d y, rfl⟩
  exact properCycle_intrinsic_support_component_point_ne_zero X γ ξ hξ d hdim e he u hu
    (hother u.underlying y.underlying.property)

end HodgeLean.Foundations.QuotientDuality
