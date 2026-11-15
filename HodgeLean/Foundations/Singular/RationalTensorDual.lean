import HodgeLean.Foundations.Singular.RationalDualComparison
import HodgeLean.Foundations.Singular.RationalTensorZero

/-! Dual-cohomology transport to actual tensor degrees of rational homology quotients. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- Actual tensor dual cohomology is identified with functionals on the tensor degree of homology quotients.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient algebraic Künneth argument. -/
def rationalTensorDualHomologyEquiv (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    ((HomologicalComplex.tensorObj K L).sc n).linearDual.homology ≃ₗ[ℚ]
      Module.Dual ℚ ((HomologicalComplex.tensorObj
        (rationalHomologyComplex K) (rationalHomologyComplex L)).X n) :=
  (rationalDualCohomologyHomotopyEquiv (rationalTensorHomologyHomotopyEquiv K L) n).symm.trans
    (rationalZeroDifferentialDualEquiv
      (HomologicalComplex.tensorObj (rationalHomologyComplex K) (rationalHomologyComplex L))
      (rationalTensorHomology_d_eq_zero K L) n)

#print axioms rationalTensorDualHomologyEquiv
end HodgeLean.Foundations.Singular
