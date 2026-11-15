import HodgeLean.Foundations.Singular.RationalDualComparison
import Mathlib.LinearAlgebra.Dual.Lemmas

/-! Finite rational homology quotients detected by actual dual cohomology. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Finite actual rational dual cohomology gives finite-dimensional actual homology quotients.
Source: Hatcher, Algebraic Topology, §3.1, the field universal-coefficient pairing. -/
theorem rationalHomologyQuotient_finite (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    [Module.Finite ℚ (K.sc n).linearDual.homology] :
    Module.Finite ℚ (rationalHomologyQuotient K n) := by
  letI : Module.Finite ℚ (Module.Dual ℚ (rationalHomologyQuotient K n)) :=
    Module.Finite.of_surjective (rationalHomologyDualEquiv K n).toLinearMap
      (rationalHomologyDualEquiv K n).surjective
  exact (Module.finite_dual_iff ℚ).mp inferInstance

#print axioms rationalHomologyQuotient_finite
end HodgeLean.Foundations.Singular
