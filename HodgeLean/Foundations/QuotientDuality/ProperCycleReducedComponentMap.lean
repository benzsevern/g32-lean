import HodgeLean.Foundations.QuotientDuality.ProperCycleDefs
import HodgeConjecture.Lemmas.AlgebraicGeometry.Cycle.Support
import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-! # Actual morphisms between reduced cycle components -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual component immersion sends its generic point to the specified scheme point.
Source: Fulton, Intersection Theory, section 1.4, reduced integral components.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_generic_point (X : Scheme) (ξ : X) :
    cycleComponentι X ξ (genericPoint (cycleComponent X ξ)) = ξ := by
  have h := (genericPoint_spec (cycleComponent X ξ)).image (cycleComponentι X ξ).continuous
  rw [Set.image_univ, range_cycleComponentι, closure_closure] at h
  exact h.eq (by rw [isGenericPoint_def])

/-- The actual composite from a reduced component has exactly the image component's vanishing ideal as kernel.
Source: Fulton, Intersection Theory, section 1.4; Mathlib Scheme.IdealSheafData.map_vanishingIdeal.
HC no distance; AV milestone no distance. -/
lemma properCycle_component_map_kernel {X Y : Scheme} (f : X ⟶ Y) (ξ : X) :
    (cycleComponentι X ξ ≫ f).ker = (cycleComponentι Y (f ξ)).ker := by
  rw [Scheme.Hom.ker_comp]
  change ((Scheme.IdealSheafData.vanishingIdeal
    (X := X) ⟨closure {ξ}, isClosed_closure⟩).subschemeι.ker).map f =
    (Scheme.IdealSheafData.vanishingIdeal
      (X := Y) ⟨closure {f ξ}, isClosed_closure⟩).subschemeι.ker
  rw [Scheme.IdealSheafData.ker_subschemeι, Scheme.IdealSheafData.ker_subschemeι,
    Scheme.IdealSheafData.map_vanishingIdeal]
  congr 1
  apply TopologicalSpace.Closeds.ext
  change closure (f '' closure {ξ}) = closure {f ξ}
  rw [closure_image_closure f.continuous, Set.image_singleton]

/-- A scheme morphism induces its literal morphism between the reduced source and image components.
Source: Fulton, Intersection Theory, section 1.4, the map of integral subvarieties.
HC no distance; AV milestone no distance. -/
def properCycle_reduced_component_map {X Y : Scheme} (f : X ⟶ Y) (ξ : X) :
    cycleComponent X ξ ⟶ cycleComponent Y (f ξ) :=
  IsClosedImmersion.lift (cycleComponentι Y (f ξ)) (cycleComponentι X ξ ≫ f)
    (properCycle_component_map_kernel f ξ).symm.le

/-- The induced reduced-component map retains its original ambient scheme composite.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_component_map_ι {X Y : Scheme} (f : X ⟶ Y) (ξ : X) :
    properCycle_reduced_component_map f ξ ≫ cycleComponentι Y (f ξ) = cycleComponentι X ξ ≫ f :=
  IsClosedImmersion.lift_fac _ _ _

/-- The reduced-component map sends the actual generic point to the actual image generic point.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_component_map_generic {X Y : Scheme} (f : X ⟶ Y) (ξ : X) :
    properCycle_reduced_component_map f ξ (genericPoint (cycleComponent X ξ)) =
      genericPoint (cycleComponent Y (f ξ)) := by
  apply (cycleComponentι Y (f ξ)).isClosedEmbedding.injective
  have h := congrArg (fun g : cycleComponent X ξ ⟶ Y => g (genericPoint (cycleComponent X ξ)))
    (properCycle_reduced_component_map_ι f ξ)
  change cycleComponentι Y (f ξ)
      (properCycle_reduced_component_map f ξ (genericPoint (cycleComponent X ξ))) =
    f (cycleComponentι X ξ (genericPoint (cycleComponent X ξ))) at h
  rw [properCycle_component_generic_point] at h
  exact h.trans (properCycle_component_generic_point Y (f ξ)).symm

end HodgeLean.Foundations.QuotientDuality
