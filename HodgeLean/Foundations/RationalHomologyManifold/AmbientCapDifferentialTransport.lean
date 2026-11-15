import HodgeLean.Foundations.RationalHomologyManifold.AmbientCochainSheafComplex
import HodgeLean.Foundations.RationalHomologyManifold.AmbientFixedCapSheafDifferential

/-! Equality transport of the actual fixed-cycle cap differential.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- The actual fixed-cycle cap differential is unchanged by the equality identifying its total degree.
Source: Hatcher, Algebraic Topology, section 3.3; equality transport of the signed cap boundary formula.
HC no distance; AV milestone no distance.
-/
theorem ambientFixedCapSheafMap_coboundary_cast (X : TopCat.{0}) (N p q : ℕ)
    (z : (SingularChainComplex ℚ X).X N)
    (hz : ∀ j, (SingularChainComplex ℚ X).d N j z = 0) (hN : p + (q + 1) = N) :
    (ambientCochainSheafComplex X).d p (p + 1) ≫
      ambientFixedCapSheafMap X (p + 1) q
        (((SingularChainComplex ℚ X).XIsoOfEq (by omega : N = p + 1 + q)).hom z) =
      (-1 : ℤ) ^ (p + 1) • (ambientFixedCapSheafMap X p (q + 1)
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z) ≫
          (subdivisionLimitSheafComplex X).d (q + 1) q) := by
  subst N
  exact ambientFixedCapSheafMap_coboundary X p q z (hz (p + q))

#print axioms ambientFixedCapSheafMap_coboundary_cast
end HodgeLean.Foundations.RationalHomologyManifold
