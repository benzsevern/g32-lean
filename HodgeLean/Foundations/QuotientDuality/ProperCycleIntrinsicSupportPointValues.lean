import HodgeLean.Foundations.QuotientDuality.ProperCycleIsolatedComponentSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentOnSupport
import HodgeLean.Foundations.QuotientDuality.ProperCycleHomologyImagePointValues

/-! # Actual intrinsic component point values inside literal cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace Topology
open HodgeLean.Adapters HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- A specified intrinsic support component has zero original local value away from that prime's actual analytic support.
Source: properCycle_local_orientation_image_outside_range; properCycle_component_support_map_range.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_component_point_zero
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ))
    (z : a3b4_cycleSupport X.hom γ) (hz : z.val.underlying ∉ closure ({ξ} : Set X.left)) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)
      (properCycle_intrinsic_component_on_support X γ ξ hξ d hdim) z = 0 := by
  let V := properCycle_component_over X ξ
  have hVdim : topologicalKrullDim V.left = (d : ℕ) := hdim
  let a := properCycle_intrinsic_class V d hVdim
  let f := properCycle_component_support_map X γ ξ hξ
  have hnot : z ∉ Set.range f := by
    rw [properCycle_component_support_map_range]
    exact hz
  change localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)
    (homologyMap ℚ (2*d) f a) z = 0
  exact properCycle_local_orientation_image_outside_range f z hnot (2*d) a

/-- At an actual isolated holomorphic point of its reduced component, the specified intrinsic class has nonzero original point value inside the literal cycle support.
Source: properCycle_intrinsic_class_chart; properCycle_local_orientation_image_ne_zero.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_support_component_point_ne_zero
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ))
    (e : OpenPartialHomeomorph (ComplexPoint (properCycle_component_over X ξ)) (Fin d → ℂ))
    (he : ∀ i, (f4_analytification (properCycle_component_over X ξ)).IsHolFun
      (fun z : e.source => e z i))
    (y : ComplexPoint (properCycle_component_over X ξ)) (hy : y ∈ e.source)
    (hother : ∀ η ∈ γ.support, η ≠ ξ →
      (Point.map (properCycle_component_over_inclusion X ξ) y).underlying ∉
        closure ({η} : Set X.left)) :
    localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)
      (properCycle_intrinsic_component_on_support X γ ξ hξ d hdim)
      (properCycle_component_support_map X γ ξ hξ y) ≠ 0 := by
  let V := properCycle_component_over X ξ
  letI : T2Space (ComplexPoint X) := f4_t2Space X
  letI : T2Space (a3b4_an X.hom) := f4_t2Space X
  letI : T2Space (ComplexPoint V) := f4_t2Space V
  have hVdim : topologicalKrullDim V.left = (d : ℕ) := hdim
  let a := properCycle_intrinsic_class V d hVdim
  let f := properCycle_component_support_map X γ ξ hξ
  have hf := properCycle_component_support_map_embedding X γ ξ hξ
  have hnb := properCycle_isolated_component_support_neighborhood X γ ξ hξ (f y) hother
  have hn := properCycle_intrinsic_class_chart V d hVdim e he y hy
  have ha : localOrientation (TopCat.of (ComplexPoint V)) (2*d) a y ≠ 0 := by
    intro hz
    exact localClassOfChart_ne_zero d e y hy (hn.symm.trans hz)
  change localOrientation (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d)
    (homologyMap ℚ (2*d) f a) (f y) ≠ 0
  exact properCycle_local_orientation_image_ne_zero f hf y hnb (2*d) a ha

end HodgeLean.Foundations.QuotientDuality
