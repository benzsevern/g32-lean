import HodgeLean.Foundations.QuotientDuality.ProperCycleZeroOrientationPushforward
import HodgeLean.Foundations.QuotientDuality.RetainedCycleIntrinsicDegree

/-! # The intrinsic zero-dimensional component image

Consumer: RetainedCycleConsumerSteps.lean:42, through RetainedCycleProofs.lean:249.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

/-- In dimension zero the actual intrinsic component image equals the specified complex-normalized ambient class. -/
lemma retained_zero_intrinsic_component_image
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsProjective X.hom]
    (hdim : TopologicalSpace.dim X.left = 0)
    (c : Homology ℚ (a3b4_an X.hom) 0)
    (hn : ∀ (E : OpenPartialHomeomorph (ComplexPoint X) (Fin 0 → ℂ)),
      (∀ j, (f4_analytification X).IsHolFun (fun u : E.source => E u j)) →
      ∀ x (hx : x ∈ E.source), localOrientation (a3b4_an X.hom) 0 c x =
        localClassOfChart 0 E x hx)
    (ξ : X.left) (hc : Order.coheight ξ = 0) :
    properCycle_intrinsic_component X 0 ξ = c := by
  have hdZ := properCycle_middle_component_dimension X 0 hdim ξ hc
  have hd0 : TopologicalSpace.dim (intrinsicComponent X ξ).left = 0 := by
    change ((topologicalKrullDim (cycleComponent X.left ξ)).unbotD 0).toNat = 0
    rw [hdZ]
    rfl
  have hp := properCycle_zero_dimension_orientation_pushforward
    (intrinsicComponentInclusion X ξ) hd0 hdim
    (retainedIntrinsicFundamentalClass X 0 hdim ξ hc)
    (properCycle_intrinsic_class_chart (intrinsicComponent X ξ) 0 hdZ) c hn
  rw [properCycle_intrinsic_component_eq_image X 0 ξ hdZ]
  exact hp

end HodgeLean.Foundations.QuotientDuality
