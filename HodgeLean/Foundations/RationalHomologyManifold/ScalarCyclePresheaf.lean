import HodgeLean.Foundations.RationalHomologyManifold.ScalarChainPresheaf
import HodgeLean.RealDefs.Port.AlgebraicTopology.Sheaf.HomologySection

/-! Actual scalar cycle classes in the original supported presheaf.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- An actual ambient cycle gives a scalar cycle morphism on the original supported-chain presheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; supported relative cycle representatives.
HC no distance; AV milestone no distance.
-/
theorem scalarChainPresheafMap_cycle (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) :
    scalarChainPresheafMap X (n + 1) z ≫ (singularChainPresheafComplex ℚ X).d (n + 1) n = 0 := by
  rw [scalarChainPresheafMap_boundary, hz]
  apply NatTrans.ext
  funext U
  ext r
  change ℚ at r
  change (relativeChainProjection ℚ (TopPair.ofSubset (X := X) (U.unop : Set X)ᶜ)).f n (r • 0) = 0
  rw [smul_zero, map_zero]

#print axioms scalarChainPresheafMap_cycle
/-- Take the actual homology class of the scalar supported cycle in the original chain presheaf.
Source: Bredon, Sheaf Theory, second edition, VI.12; actual relative homology classes on open supports.
HC no distance; AV milestone no distance.
-/
def scalarCycleHomologyPresheafMap (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) :
    TopCat.Presheaf.const X (AddCommGrpCat.of ℚ) ⟶
      (singularChainPresheafComplex ℚ X).homology (n + 1) :=
  (singularChainPresheafComplex ℚ X).liftCycles (scalarChainPresheafMap X (n + 1) z)
    n (ChainComplex.next_nat_succ n) (scalarChainPresheafMap_cycle X n z hz) ≫
      (singularChainPresheafComplex ℚ X).homologyπ (n + 1)

#print axioms scalarCycleHomologyPresheafMap
/-- Exact sheafification carries the actual scalar cycle class to the original supported homology sheaf.
Source: Bredon, Sheaf Theory, second edition, I.1 and VI.12; exact homology sheafification.
HC no distance; AV milestone no distance.
-/
def scalarCycleHomologySheafMap (X : TopCat.{0}) (n : ℕ)
    (z : (SingularChainComplex ℚ X).X (n + 1))
    (hz : (SingularChainComplex ℚ X).d (n + 1) n z = 0) :
    TopCat.Sheaf.const X (AddCommGrpCat.of ℚ) ⟶ singularChainHomologySheaf ℚ X (n + 1) :=
  (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).map
      (scalarCycleHomologyPresheafMap X n z hz) ≫
    (singularChainHomologySheafificationIso ℚ X (n + 1)).hom

#print axioms scalarCycleHomologySheafMap
end HodgeLean.Foundations.RationalHomologyManifold
