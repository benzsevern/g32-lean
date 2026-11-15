import HodgeLean.Foundations.Singular.RationalHomologyMaps

/-! The actual graded rational homology quotient as a zero-differential chain complex. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Singular

/-- The actual cycle quotients of a rational complex, with every differential zero.
Source: Hatcher, Algebraic Topology, §3.2, splitting complexes over a field. -/
def rationalHomologyComplex (K : ChainComplex (ModuleCat ℚ) ℕ) : ChainComplex (ModuleCat ℚ) ℕ where
  X n := ModuleCat.of ℚ (rationalHomologyQuotient K n)
  d _ _ := 0
  shape _ _ _ := rfl
  d_comp_d' _ _ _ _ _ := by simp

#print axioms rationalHomologyComplex
end HodgeLean.Foundations.Singular
