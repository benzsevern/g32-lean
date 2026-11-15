import HodgeLean.Foundations.Singular.RationalChainContraction

/-! The positive-degree contraction identity for actual rational chains. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The contraction and chosen homology representative recover every positive-degree rational chain.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
theorem rationalChainContraction_identity_succ (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (z : K.X (n + 1)) :
    rationalChainContraction K n ((K.d (n + 1) n).hom z) +
      (K.d (n + 2) (n + 1)).hom (rationalChainContraction K (n + 1) z) +
        rationalHomologyInclusion K (n + 1) (rationalHomologyProjection K (n + 1) z) = z := by
  rw [rationalChainContraction_of_boundary, rationalChainContraction_boundary]
  change rationalChainBoundarySection K n ((K.d (n + 1) n).hom.rangeRestrict z) +
    (z - rationalChainBoundarySection K n ((K.d (n + 1) n).hom.rangeRestrict z) -
      rationalHomologyInclusion K (n + 1) (rationalHomologyProjection K (n + 1) z)) +
    rationalHomologyInclusion K (n + 1) (rationalHomologyProjection K (n + 1) z) = z
  abel

#print axioms rationalChainContraction_identity_succ
end HodgeLean.Foundations.Singular
