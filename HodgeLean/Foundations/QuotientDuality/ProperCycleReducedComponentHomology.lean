import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedComponentOver
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicImage

/-! # Actual singular homology squares for reduced-component maps -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual reduced-component immersion with its original complex base.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
def properCycle_component_over_inclusion (X : Over (Spec ↧ℂ)) (ξ : X.left) :
    properCycle_component_over X ξ ⟶ X :=
  Over.homMk (cycleComponentι X.left ξ) rfl

/-- The reduced-component square commutes over the original complex base.
Source: Fulton, Intersection Theory, section 1.4.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_component_over_square {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (ξ : X.left) :
    properCycle_reduced_component_over_map f ξ ≫ properCycle_component_over_inclusion Y (f.left ξ) =
      properCycle_component_over_inclusion X ξ ≫ f := by
  apply Over.OverMorphism.ext
  exact properCycle_reduced_component_map_ι f.left ξ

/-- The literal singular image of a supplied intrinsic class respects composition of the original complex-point maps.
Source: Hatcher, Algebraic Topology, section 2.1, functorial singular homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_image_comp {V X Y : Over (Spec ↧ℂ)}
    (i : V ⟶ X) (f : X ⟶ Y) (d : ℕ)
    (c : Homology ℚ (a3b4_an V.hom) (2 * d)) :
    properCycle_intrinsic_image (i ≫ f) d c =
      properCycle_intrinsic_image f d (properCycle_intrinsic_image i d c) := by
  have hf : TopCat.ofHom (Point.continuousMap (i ≫ f)) =
      TopCat.ofHom (Point.continuousMap i) ≫ TopCat.ofHom (Point.continuousMap f) := by
    ext z : 1
    rfl
  unfold properCycle_intrinsic_image
  rw [hf, homologyMap_comp]
  rfl

/-- Actual component inclusion and actual ambient pushforward give the same homology image as the constructed reduced-component map followed by the image inclusion.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1, functorial component pushforward.
HC no distance; AV milestone no distance. -/
lemma properCycle_reduced_component_homology_square {X Y : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (ξ : X.left) (d : ℕ)
    (c : Homology ℚ (a3b4_an (properCycle_component_over X ξ).hom) (2 * d)) :
    properCycle_intrinsic_image f d
      (properCycle_intrinsic_image (properCycle_component_over_inclusion X ξ) d c) =
    properCycle_intrinsic_image (properCycle_component_over_inclusion Y (f.left ξ)) d
      (properCycle_intrinsic_image (properCycle_reduced_component_over_map f ξ) d c) := by
  rw [← properCycle_intrinsic_image_comp, ← properCycle_intrinsic_image_comp,
    properCycle_reduced_component_over_square]

end HodgeLean.Foundations.QuotientDuality
