import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafUnit

/-! Actual local restriction of the ambient singular cup unit.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual singular cup unit is the coefficient-summing augmentation on zero-chains.
Source: Hatcher, Algebraic Topology, section 3.2; the value one on each singular vertex.
HC no distance; AV milestone no distance.
-/
theorem singular_unit_eq_zeroAugmentation (X : TopCat.{0}) :
    HodgeLean.Foundations.Singular.unitCochain (R := ℚ) X =
      (simplicialZeroAugmentation ℚ (TopCat.toSSet.obj X)).hom := by
  rfl

#print axioms singular_unit_eq_zeroAugmentation
/-- Restricting scalar multiples of the actual ambient unit gives the original constant local zero-cochain morphism.
Source: Hatcher, Algebraic Topology, section 3.2; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem ambientConstantsToZeroPresheaf_restriction (X : TopCat.{0}) :
    ambientConstantsToZeroPresheaf X ≫ ambientCochainPresheafRestriction X 0 =
      constantsToSingularCochainZero ℚ X := by
  apply NatTrans.ext
  funext U
  ext r
  change ℚ at r
  apply LinearMap.ext
  intro c
  change r * HodgeLean.Foundations.Singular.unitCochain X
      (((singularChainComplexMap ℚ (Opens.inclusion' U.unop)).f 0).hom c) =
    r * (openZeroAugmentation ℚ X U).hom c
  rw [singular_unit_eq_zeroAugmentation]
  exact congrArg (r * ·) (congrArg (fun f => f.hom c)
    (simplicialZeroAugmentation_naturality ℚ (TopCat.toSSet.map (Opens.inclusion' U.unop))))

#print axioms ambientConstantsToZeroPresheaf_restriction
/-- The actual sheafified ambient unit restricts to the original constant local singular cochain morphism.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; exact sheafification of unit restriction.
HC no distance; AV milestone no distance.
-/
theorem ambientConstantsToZeroSheaf_restriction (X : TopCat.{0}) :
    ambientConstantsToZeroSheaf X ≫ (ambientCochainSheafRestriction X).f 0 =
      constantsToSingularCochainZeroSheaf ℚ X := by
  let F := presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}
  change F.map (ambientConstantsToZeroPresheaf X) ≫
    F.map (ambientCochainPresheafRestriction X 0) = F.map (constantsToSingularCochainZero ℚ X)
  rw [← F.map_comp, ambientConstantsToZeroPresheaf_restriction]

#print axioms ambientConstantsToZeroSheaf_restriction
end HodgeLean.Foundations.RationalHomologyManifold
