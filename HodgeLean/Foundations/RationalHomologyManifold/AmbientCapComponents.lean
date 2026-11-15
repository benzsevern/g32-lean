import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafComplex
import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCapSheaf
import HodgeLean.Foundations.RationalHomologyManifold.CapTargetZeroTerm

/-! The actual fixed-chain cap components in the bounded orientation target.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Use literal cap in each complementary degree, its actual top boundary quotient in degree zero, and zero beyond the total degree.
Source: Hatcher, Algebraic Topology, section 3.3; Bredon, Sheaf Theory, second edition, VI.12.
HC no distance; AV milestone no distance.
-/
def ambientCapTargetComponent (X : TopCat.{0}) (N : ℕ)
    (z : (SingularChainComplex ℚ X).X N) (p : ℕ) :
    (ambientCochainSheafComplex X).X p ⟶ (capTargetComplex X N).X p := by
  classical
  by_cases hp : p = 0
  · subst p
    exact ambientFixedCapSheafMap X 0 N
      (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = 0 + N)).hom z) ≫
      (subdivisionLimitSheafComplex X).pOpcycles N ≫ (capTargetZeroTermIso X N).inv
  · by_cases hN : p ≤ N
    · exact ambientFixedCapSheafMap X p (N - p)
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = p + (N - p))).hom z) ≫
        (capTargetTermIso X N p (N - p) (by omega) (by omega)).inv
    · exact 0

#print axioms ambientCapTargetComponent
end HodgeLean.Foundations.RationalHomologyManifold
