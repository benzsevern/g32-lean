import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicSingularProperDegree
import HodgeLean.Foundations.QuotientDuality.ProperCycleIntrinsicComponentComparison
import HodgeLean.Foundations.QuotientDuality.ProperCycleSingularComponentDimension

/-! # Original intrinsic component degree for positive residue weight -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- A positive original residue degree gives the intrinsic component pushforward through the actual reduced component morphism, with no ambient smoothness premise.
Source: Fulton, Intersection Theory, sections 1.4 and 19.1.
HC no distance; AV milestone no distance. -/
lemma properCycle_intrinsic_component_degree_pos
    {X Y : Over (Spec ↧ℂ)} [IsIntegral X.left] [IsIntegral Y.left]
    [IsProjective X.hom] [IsProjective Y.hom]
    (f : X ⟶ Y) [IsProper f.left] (k : ℕ)
    (hdimX : TopologicalSpace.dim X.left = 2 * k)
    (hdimY : TopologicalSpace.dim Y.left = 2 * k)
    (ξ : X.left) (hcodim : Order.coheight ξ = k)
    (hdegree : 0 < a1p_degree f.left ξ) :
    homologyMap ℚ (2 * k) (TopCat.ofHom (Point.continuousMap f))
      (properCycle_intrinsic_component X k ξ) =
    (a1p_degree f.left ξ : ℚ) • properCycle_intrinsic_component Y k (f.left ξ) := by
  have hcodimY : Order.coheight (f.left ξ) = k :=
    (properCycle_coheight_of_degree f (hdimX.trans hdimY.symm) ξ hdegree).trans hcodim
  have hdX := properCycle_middle_component_dimension X k hdimX ξ hcodim
  have hdY := properCycle_middle_component_dimension Y k hdimY (f.left ξ) hcodimY
  let V := properCycle_component_over X ξ
  let W := properCycle_component_over Y (f.left ξ)
  let g : V ⟶ W := properCycle_reduced_component_over_map f ξ
  have hgeneric : g.left (genericPoint V.left) = genericPoint W.left :=
    properCycle_reduced_component_map_generic f.left ξ
  have hdg : a1p_degree g.left (genericPoint V.left) = a1p_degree f.left ξ :=
    properCycle_reduced_component_residue_degree f.left ξ
  have hdegreeg : 0 < a1p_degree g.left (genericPoint V.left) := hdg.symm ▸ hdegree
  have h := properCycle_intrinsic_proper_generic_degree V W g k hdX hdY hgeneric hdegreeg
  rw [hdg] at h
  change properCycle_intrinsic_image g k (properCycle_intrinsic_class V k hdX) =
    (a1p_degree f.left ξ : ℚ) • properCycle_intrinsic_class W k hdY at h
  rw [properCycle_intrinsic_component_eq_image X k ξ hdX,
    properCycle_intrinsic_component_eq_image Y k (f.left ξ) hdY]
  change properCycle_intrinsic_image f k
    (properCycle_intrinsic_image (properCycle_component_over_inclusion X ξ) k
      (properCycle_intrinsic_class V k hdX)) = _
  rw [properCycle_reduced_component_homology_square]
  change homologyMap ℚ (2 * k)
    (TopCat.ofHom (Point.continuousMap (properCycle_component_over_inclusion Y (f.left ξ))))
      (properCycle_intrinsic_image g k (properCycle_intrinsic_class V k hdX)) = _
  rw [h, map_smul]
  rfl

end HodgeLean.Foundations.QuotientDuality
