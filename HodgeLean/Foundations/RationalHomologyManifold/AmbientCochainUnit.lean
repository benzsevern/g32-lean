import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafComplex
import HodgeLean.Foundations.RationalHomologyManifold.ChainCapUnit

/-! The actual cup unit in the constant ambient cochain sheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Scalar multiples of the actual singular cup unit define the ambient constant zero-cochains.
Source: Hatcher, Algebraic Topology, section 3.2; the singular cup unit.
HC no distance; AV milestone no distance.
-/
def ambientConstantsToZeroPresheaf (X : TopCat.{0}) :
    (Functor.const (Opens X)ᵒᵖ).obj (AddCommGrpCat.of ℚ) ⟶
      (ambientCochainPresheafComplex X).X 0 :=
  (Functor.const (Opens X)ᵒᵖ).map
    (AddCommGrpCat.ofHom ((LinearMap.toSpanSingleton ℚ _
      (HodgeLean.Foundations.Singular.unitCochain X)).toAddMonoidHom))

#print axioms ambientConstantsToZeroPresheaf
/-- The actual ambient cup unit has zero coboundary on every open set.
Source: Hatcher, Algebraic Topology, section 3.2; the coboundary of the cup unit.
HC no distance; AV milestone no distance.
-/
theorem ambientConstantsToZeroPresheaf_coboundary (X : TopCat.{0}) :
    ambientConstantsToZeroPresheaf X ≫ (ambientCochainPresheafComplex X).d 0 1 = 0 := by
  apply NatTrans.ext
  funext U
  ext r
  change ℚ at r
  change coboundary ℚ 0 (r • HodgeLean.Foundations.Singular.unitCochain (R := ℚ) X) = 0
  rw [map_smul, HodgeLean.Foundations.Singular.coboundary_unitCochain, smul_zero]

#print axioms ambientConstantsToZeroPresheaf_coboundary
end HodgeLean.Foundations.RationalHomologyManifold
