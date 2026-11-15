import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapComponentNormalization
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapZeroNormalization
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapDifferentialTransport
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetZeroBoundary

/-! The actual fixed-cycle cap differential in degree zero.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual bounded cap component in degree zero commutes with the first cochain differential.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
theorem ambientCapTargetComponent_comm_zero (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : ∀ j, (SingularChainComplex ℚ X).d (n + 1) j z = 0) :
    (ambientCochainSheafComplex X).d 0 1 ≫ ambientCapTargetComponent X (n + 1) z 1 =
      ambientCapTargetComponent X (n + 1) z 0 ≫ (capTargetComplex X (n + 1)).d 0 1 := by
  let e := capTargetTermIso X (n + 1) 1 n (by omega) (by omega)
  apply (cancel_mono e.hom).mp
  calc
    _ = (ambientCochainSheafComplex X).d 0 1 ≫
        ambientFixedCapSheafMap X 1 n
          (((SingularChainComplex ℚ X).XIsoOfEq (by omega : n + 1 = 1 + n)).hom z) := by
      rw [Category.assoc, ambientCapTargetComponent_positive X (n + 1) 1 n z (by omega) (by omega)]
    _ = -(ambientFixedCapSheafMap X 0 (n + 1)
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : n + 1 = 0 + (n + 1))).hom z) ≫
          (subdivisionLimitSheafComplex X).d (n + 1) n) := by
      simpa only [Nat.reduceAdd, pow_one, neg_one_zsmul] using
        ambientFixedCapSheafMap_coboundary_cast X (n + 1) 0 n z hz (by omega)
    _ = -((ambientCapTargetComponent X (n + 1) z 0 ≫ (capTargetZeroTermIso X (n + 1)).hom) ≫
        (subdivisionLimitSheafComplex X).fromOpcycles (n + 1) n) := by
      rw [ambientCapTargetComponent_zero, Category.assoc, HomologicalComplex.p_fromOpcycles]
    _ = _ := by
      have ht := congrArg (fun f => ambientCapTargetComponent X (n + 1) z 0 ≫ f)
        (capTargetZeroTermIso_boundary X n)
      simpa only [Category.assoc, Preadditive.comp_neg] using ht.symm

#print axioms ambientCapTargetComponent_comm_zero
end HodgeLean.Foundations.RationalHomologyManifold
