import HodgeLean.Foundations.QuotientDuality.ProperCycleComponentSupportMap

/-! # Specified intrinsic component classes on original cycle supports
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- The specified intrinsic class of an actual reduced component, carried into the literal original cycle support by its actual immersion.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1, intrinsic fundamental classes of prime components.
HC no distance; AV milestone no distance. -/
def properCycle_intrinsic_component_on_support
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ)) :
    Homology ℚ (TopCat.of (a3b4_cycleSupport X.hom γ)) (2*d) :=
  homologyMap ℚ (2*d) (properCycle_component_support_map X γ ξ hξ)
    (properCycle_intrinsic_class (properCycle_component_over X ξ) d hdim)

/-- The literal support inclusion carries this class to the original specified intrinsic component class.
Source: properCycle_intrinsic_component_eq_image; actual functoriality of singular homology.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_component_on_support_inclusion
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] (γ : AlgebraicCycle X.left ℚ)
    (ξ : X.left) (hξ : ξ ∈ γ.support) (d : ℕ)
    (hdim : topologicalKrullDim (cycleComponent X.left ξ) = (d : ℕ)) :
    homologyMap ℚ (2*d) (TopPair.ofSubset (X := a3b4_an X.hom)
      (a3b4_cycleSupport X.hom γ)).map
      (properCycle_intrinsic_component_on_support X γ ξ hξ d hdim) =
      properCycle_intrinsic_component X d ξ := by
  let V := properCycle_component_over X ξ
  have hVdim : topologicalKrullDim V.left = (d : ℕ) := hdim
  let a := properCycle_intrinsic_class V d hVdim
  let i := (TopPair.ofSubset (X := a3b4_an X.hom) (a3b4_cycleSupport X.hom γ)).map
  change homologyMap ℚ (2*d) i
    (homologyMap ℚ (2*d) (properCycle_component_support_map X γ ξ hξ) a) = _
  calc
    _ = homologyMap ℚ (2*d) (properCycle_component_support_map X γ ξ hξ ≫ i) a :=
      (LinearMap.congr_fun (homologyMap_comp ℚ (2*d)
        (properCycle_component_support_map X γ ξ hξ) i) a).symm
    _ = _ := by
      rw [show properCycle_component_support_map X γ ξ hξ ≫ i =
        TopCat.ofHom (Point.continuousMap (properCycle_component_over_inclusion X ξ)) from
        properCycle_component_support_map_inclusion X γ ξ hξ]
      exact (properCycle_intrinsic_component_eq_image X d ξ hdim).symm

end HodgeLean.Foundations.QuotientDuality
