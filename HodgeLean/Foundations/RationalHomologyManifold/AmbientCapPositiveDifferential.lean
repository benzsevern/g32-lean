import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapComponentNormalization
import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapDifferentialTransport
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetBoundary

/-! Actual bounded fixed-cycle cap commutation in positive complementary degrees.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual bounded fixed-cycle cap components commute with differentials in every positive interior degree.
Source: Hatcher, Algebraic Topology, section 3.3; the literal cap boundary formula in the bounded supported-chain model.
HC no distance; AV milestone no distance.
-/
theorem ambientCapTargetComponent_comm_positive (X : TopCat.{0}) (N p q : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0)
    (hp : 0 < p) (hN : p + (q + 1) = N) :
    (ambientCochainSheafComplex X).d p (p + 1) ≫ ambientCapTargetComponent X N z (p + 1) =
      ambientCapTargetComponent X N z p ≫ (capTargetComplex X N).d p (p + 1) := by
  let e := capTargetTermIso X N (p + 1) q (by omega) (by omega)
  apply (cancel_mono e.hom).mp
  calc
    _ = (ambientCochainSheafComplex X).d p (p + 1) ≫
        ambientFixedCapSheafMap X (p + 1) q
          (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = p + 1 + q)).hom z) := by
      rw [Category.assoc, ambientCapTargetComponent_positive X N (p + 1) q z (by omega) (by omega)]
    _ = (-1 : ℤ) ^ (p + 1) • (ambientFixedCapSheafMap X p (q + 1)
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z) ≫
          (subdivisionLimitSheafComplex X).d (q + 1) q) :=
      ambientFixedCapSheafMap_coboundary_cast X N p q z hz hN
    _ = (-1 : ℤ) ^ (p + 1) • ((ambientCapTargetComponent X N z p ≫
        (capTargetTermIso X N p (q + 1) hp hN).hom) ≫
          (subdivisionLimitSheafComplex X).d (q + 1) q) := by
      rw [ambientCapTargetComponent_positive X N p (q + 1) z hp hN]
    _ = _ := by
      have ht := congrArg (fun f => ambientCapTargetComponent X N z p ≫ f)
        (capTargetTermIso_boundary X N p q hp hN)
      simpa only [Category.assoc, Preadditive.comp_zsmul] using ht.symm

#print axioms ambientCapTargetComponent_comm_positive
end HodgeLean.Foundations.RationalHomologyManifold
