import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedComponentDegree

/-! # Reduced-component maps over the actual complex base -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual reduced component with the original complex structure morphism.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
def properCycle_component_over (X : Over (Spec ↧ℂ)) (ξ : X.left) : Over (Spec ↧ℂ) :=
  Over.mk (cycleComponentι X.left ξ ≫ X.hom)

instance properCycle_component_over_integral (X : Over (Spec ↧ℂ)) (ξ : X.left) :
    IsIntegral (properCycle_component_over X ξ).left := by
  change IsIntegral (cycleComponent X.left ξ)
  infer_instance

instance properCycle_component_over_projective (X : Over (Spec ↧ℂ)) [IsProjective X.hom]
    (ξ : X.left) : IsProjective (properCycle_component_over X ξ).hom := by
  rcases ‹IsProjective X.hom›.nonempty_presentation with ⟨P⟩
  exact ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := cycleComponentι X.left ξ ≫ P.immersion
      isClosedImmersion := by
        letI := P.isClosedImmersion
        infer_instance
      immersion_toBase := by rw [Category.assoc, P.immersion_toBase]; rfl }
  ⟩⟩

/-- The literal reduced-component morphism respects the original complex base.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
def properCycle_reduced_component_over_map {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (ξ : X.left) :
    properCycle_component_over X ξ ⟶ properCycle_component_over Y (f.left ξ) :=
  Over.homMk (properCycle_reduced_component_map f.left ξ) (by
    change properCycle_reduced_component_map f.left ξ ≫
      (cycleComponentι Y.left (f.left ξ) ≫ Y.hom) = cycleComponentι X.left ξ ≫ X.hom
    rw [← Category.assoc, properCycle_reduced_component_map_ι, Category.assoc, Over.w f])

/-- Properness descends to the induced map of the actual reduced components.
Source: Stacks Project, Tag 01W0, proper morphisms and separated cancellation.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_component_map_proper {X Y : Scheme.{0}}
    (f : X ⟶ Y) [IsProper f] (ξ : X) : IsProper (properCycle_reduced_component_map f ξ) := by
  have h : IsProper (properCycle_reduced_component_map f ξ ≫ cycleComponentι Y (f ξ)) := by
    rw [properCycle_reduced_component_map_ι]
    infer_instance
  exact IsProper.of_comp _ (cycleComponentι Y (f ξ))

instance properCycle_reduced_component_over_map_proper {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) [IsProper f.left] (ξ : X.left) :
    IsProper (properCycle_reduced_component_over_map f ξ).left :=
  properCycle_reduced_component_map_proper f.left ξ

end HodgeLean.Foundations.QuotientDuality
