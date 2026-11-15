import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedComponentHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicClassProperties

/-! # Original intrinsic components through their actual reduced immersions -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- In its intrinsic dimension the original component class is the specified class of the actual reduced component, pushed through the literal component immersion.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_component_eq_image
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (d : ℕ) (ξ : X.left)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ)) :
    properCycle_intrinsic_component X d ξ =
      properCycle_intrinsic_image (properCycle_component_over_inclusion X ξ) d
        (properCycle_intrinsic_class (properCycle_component_over X ξ) d hdim) := by
  unfold properCycle_intrinsic_component
  dsimp only
  split_ifs with h
  · rfl
  · exact (h hdim).elim

end HodgeLean.Foundations.QuotientDuality
