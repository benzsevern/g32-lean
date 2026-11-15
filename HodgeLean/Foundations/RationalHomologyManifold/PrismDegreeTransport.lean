import HodgeLean.Foundations.RationalHomologyManifold.PrismCapStabilization

/-! Actual degree transport for the finite prism family.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular AlgebraicTopology.Simplicial
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Reassociation transports the actual prism component to the same output degree as the cap by a coboundary.
Source: Hatcher, Algebraic Topology, sections 2.1 and 3.3; transport of the actual chain degree.
HC no distance; AV milestone no distance.
-/
theorem rationalPrismSum_reassoc (X : TopCat.{0}) (n p q m : ℕ)
    (z : (SingularChainComplex ℚ X).X n) :
    reassocChain ℚ p q (rationalPrismSum X n (p + q + 1) m z) =
      rationalPrismSum X n (p + 1 + q) m z := by
  have h (i j : ℕ) (hij : i = j) :
      ((SingularChainComplex ℚ X).XIsoOfEq hij).hom
          (rationalPrismSum X n i m z) = rationalPrismSum X n j m z := by
    subst j
    simp
  exact h _ _ (by omega)

#print axioms rationalPrismSum_reassoc
end HodgeLean.Foundations.RationalHomologyManifold
