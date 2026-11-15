import HodgeLean.Foundations.Singular.ProductInverseProduct

/-! The actual rational Eilenberg–Zilber chain homotopy equivalence. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Actual rational product chains are chain homotopy equivalent to the actual total tensor complex.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber theorem. -/
def rationalProductTensorHomotopyEquiv (X Y : TopCat.{0}) :
    HomotopyEquiv (rationalTensorChains X Y) (rationalProductChains X Y) where
  hom := tensorProductComparison X Y
  inv := productAlexanderWhitney X Y
  homotopyHomInvId := tensorComparisonHomotopy X Y
  homotopyInvHomId := productComparisonHomotopy X Y

#print axioms rationalProductTensorHomotopyEquiv
end HodgeLean.Foundations.Singular
