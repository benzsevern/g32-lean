import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedComponentMap
import HodgeLean.Adapters.CyclePushforwardProduct

/-! # Residue degrees of actual reduced-component morphisms -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry HodgeLean.Adapters TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- Closed immersions have their literal residue-field degree one at every point.
Source: Fulton, Intersection Theory, section 1.4; Mathlib, surjectivity of closed-immersion stalk maps.
HC no distance; AV milestone no distance. -/
lemma properCycle_closed_immersion_degree {X Y : Scheme.{0}}
    (i : X ⟶ Y) [IsClosedImmersion i] (x : X) : a1p_degree i x = 1 := by
  apply a1x_degree_eq_one_of_surjective
  intro a
  obtain ⟨s, hs⟩ := X.residue_surjective x a
  obtain ⟨t, ht⟩ := i.stalkMap_surjective x s
  refine ⟨Y.residue (i x) t, ?_⟩
  have h := ConcreteCategory.congr_hom (Scheme.residue_residueFieldMap i x) t
  change i.residueFieldMap x (Y.residue (i x) t) = X.residue x (i.stalkMap x t) at h
  rw [ht, hs] at h
  exact h

/-- Passing to the actual reduced source and image components preserves the original residue degree at their generic points.
Source: Fulton, Intersection Theory, section 1.4, degree of an integral subvariety over its image.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_component_residue_degree {X Y : Scheme.{0}} (f : X ⟶ Y) (ξ : X) :
    a1p_degree (properCycle_reduced_component_map f ξ)
      (genericPoint (cycleComponent X ξ)) = a1p_degree f ξ := by
  have h := congrArg (fun g : cycleComponent X ξ ⟶ Y =>
    a1p_degree g (genericPoint (cycleComponent X ξ))) (properCycle_reduced_component_map_ι f ξ)
  rw [a1p_degree_comp, a1p_degree_comp,
    properCycle_closed_immersion_degree (cycleComponentι Y (f ξ)),
    properCycle_closed_immersion_degree (cycleComponentι X ξ),
    properCycle_component_generic_point, mul_one, one_mul] at h
  exact h

end HodgeLean.Foundations.QuotientDuality
