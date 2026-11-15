import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCapSheaf
import HodgeLean.Foundations.RationalHomologyManifold.ChainCapUnit

/-! The actual fixed cap unit at subdivision stage zero.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- On every open support, literal cap by the ambient cup unit is the original stage-zero supported section of the specified chain.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem ambientFixedCapPresheafMap_unit (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) (U : Opens X) :
    (ambientFixedCapPresheafMap X 0 N
      (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z)).app
        (Opposite.op U) (HodgeLean.Foundations.Singular.unitCochain X) =
      subdivisionAmbientSectionMap X N U 0 z := by
  change subdivisionAmbientSectionMap X N U 0
    (cap ℚ 0 N (HodgeLean.Foundations.Singular.unitCochain X)
      (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z)) = _
  rw [chain_cap_unit]
  change subdivisionAmbientSectionMap X N U 0
    (((SingularChainComplex ℚ X).XIsoOfEq (Nat.zero_add N)).hom
      (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z)) = _
  have he : (SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N) =
      ((SingularChainComplex ℚ X).XIsoOfEq (Nat.zero_add N)).symm := by
    rfl
  rw [he]
  exact congrArg (fun w => subdivisionAmbientSectionMap X N U 0 w)
    (ConcreteCategory.congr_hom (Iso.inv_hom_id _) z)

#print axioms ambientFixedCapPresheafMap_unit
end HodgeLean.Foundations.RationalHomologyManifold
