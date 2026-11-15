import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicContractedDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicDimensionVanishing

/-! # Original homology images of contracted intrinsic components -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A zero original residue weight gives zero original homology pushforward by factoring through the actual smaller-dimensional projective image component.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1; Hatcher, Algebraic Topology, section 2.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_component_contracted_image_zero
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left]
    [IsProjective X.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) (k : ℕ) (hdimX : TopologicalSpace.dim X.left = 2 * k)
    (ξ : X.left) (hcodim : Order.coheight ξ = k) (hzero : a1p_degree f.left ξ = 0) :
    homologyMap ℚ (2 * k) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_component X k ξ) = 0 := by
  have hdX := properCycle_middle_component_dimension X k hdimX ξ hcodim
  obtain ⟨m, hmk, hdimW⟩ := properCycle_intrinsic_contracted_component_dimension f k hdimX ξ hcodim hzero
  let V := properCycle_component_over X ξ
  let W := properCycle_component_over Y (f.left ξ)
  let g : V ⟶ W := properCycle_reduced_component_over_map f ξ
  letI : Subsingleton (Homology ℚ (a3b4_an W.hom) (2 * k)) :=
    properCycle_projective_homology_above_dimension W m hdimW (2 * k) (by omega)
  have hz : properCycle_intrinsic_image g k (properCycle_intrinsic_class V k hdX) = 0 :=
    Subsingleton.elim _ _
  rw [properCycle_intrinsic_component_eq_image X k ξ hdX]
  change properCycle_intrinsic_image f k
    (properCycle_intrinsic_image (properCycle_component_over_inclusion X ξ) k
      (properCycle_intrinsic_class V k hdX)) = 0
  rw [properCycle_reduced_component_homology_square]
  change homologyMap ℚ (2 * k)
    (TopCat.ofHom (Point.continuousMap (properCycle_component_over_inclusion Y (f.left ξ))))
      (properCycle_intrinsic_image g k (properCycle_intrinsic_class V k hdX)) = 0
  rw [hz, map_zero]

end HodgeLean.Foundations.QuotientDuality
