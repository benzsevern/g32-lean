import HodgeLean.Foundations.Singular.ProductHomotopyEquivalence
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDual

/-! Cohomology transport through the actual rational product-chain equivalence. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The actual product-chain comparison induces an equivalence of algebraic-dual cohomology groups.
Source: Hatcher, Algebraic Topology, §3.2, the Eilenberg–Zilber theorem and dual cochains. -/
def rationalProductTensorCohomologyEquiv (X Y : TopCat.{0}) (n : ℕ) :
    ((rationalProductChains X Y).sc n).linearDual.homology ≃ₗ[ℚ]
      ((rationalTensorChains X Y).sc n).linearDual.homology :=
  (CategoryTheory.ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso (rationalProductChains X Y) n)).symm.toLinearEquiv.trans
    (((HomologicalComplex.linearDualHomotopyEquiv
      (rationalProductTensorHomotopyEquiv X Y)).toHomologyIso n).toLinearEquiv.trans
      (CategoryTheory.ShortComplex.homologyMapIso
        (HomologicalComplex.linearDualCochainComplexScIso (rationalTensorChains X Y) n)).toLinearEquiv)

#print axioms rationalProductTensorCohomologyEquiv
end HodgeLean.Foundations.Singular
