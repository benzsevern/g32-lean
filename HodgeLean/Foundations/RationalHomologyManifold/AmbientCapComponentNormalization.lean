import HodgeLean.Foundations.RationalHomologyManifold.AmbientCapComponents

/-! Literal cap formulas for the actual bounded cap components.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- In each positive complementary degree, the bounded component retains the literal fixed-chain cap.
Source: Hatcher, Algebraic Topology, section 3.3; actual complementary-degree cap after regrading.
HC no distance; AV milestone no distance.
-/
theorem ambientCapTargetComponent_positive (X : TopCat.{0}) (N p q : ℕ)
    (z : (SingularChainComplex ℚ X).X N) (hp : 0 < p) (hN : p + q = N) :
    ambientCapTargetComponent X N z p ≫ (capTargetTermIso X N p q hp hN).hom =
      ambientFixedCapSheafMap X p q
        (((SingularChainComplex ℚ X).XIsoOfEq hN.symm).hom z) := by
  have hq : q = N - p := by omega
  subst q
  simp only [ambientCapTargetComponent, dif_neg (show p ≠ 0 by omega),
    dif_pos (show p ≤ N by omega), Category.assoc, Iso.inv_hom_id, Category.comp_id]

#print axioms ambientCapTargetComponent_positive
end HodgeLean.Foundations.RationalHomologyManifold
