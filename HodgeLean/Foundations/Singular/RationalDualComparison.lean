import HodgeLean.Foundations.Singular.RationalHomologyEquivalence
import HodgeLean.Foundations.Singular.RationalZeroHomology
import HodgeConjecture.Lemmas.Algebra.Homology.LinearDual

/-! Actual rational dual cohomology comparisons for split chain complexes. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- An actual rational chain homotopy equivalence induces the reversed dual-cohomology equivalence.
Source: Hatcher, Algebraic Topology, §3.1, homotopy invariance of dual cohomology. -/
def rationalDualCohomologyHomotopyEquiv {K L : ChainComplex (ModuleCat ℚ) ℕ}
    (e : HomotopyEquiv K L) (n : ℕ) :
    (L.sc n).linearDual.homology ≃ₗ[ℚ] (K.sc n).linearDual.homology :=
  (CategoryTheory.ShortComplex.homologyMapIso
    (HomologicalComplex.linearDualCochainComplexScIso L n)).symm.toLinearEquiv.trans
    (((HomologicalComplex.linearDualHomotopyEquiv e).toHomologyIso n).toLinearEquiv.trans
      (CategoryTheory.ShortComplex.homologyMapIso
        (HomologicalComplex.linearDualCochainComplexScIso K n)).toLinearEquiv)

/-- Dual cohomology of a zero-differential rational complex is the dual of its actual chain group.
Source: Hatcher, Algebraic Topology, §3.1, the field universal-coefficient pairing. -/
def rationalZeroDifferentialDualEquiv (K : ChainComplex (ModuleCat ℚ) ℕ)
    (hK : ∀ i j : ℕ, K.d i j = 0) (n : ℕ) :
    (K.sc n).linearDual.homology ≃ₗ[ℚ] Module.Dual ℚ (K.X n) :=
  ((K.sc n).linearDualHomologyEquiv).trans
    ((rationalZeroDifferentialHomologyIso K hK n).toLinearEquiv.symm.dualMap)

/-- Actual rational dual cohomology is identified with functionals on the chosen homology quotients.
Source: Hatcher, Algebraic Topology, §3.1, the field universal-coefficient pairing. -/
def rationalHomologyDualEquiv (K : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ) :
    (K.sc n).linearDual.homology ≃ₗ[ℚ] Module.Dual ℚ (rationalHomologyQuotient K n) :=
  (rationalDualCohomologyHomotopyEquiv (rationalHomologyHomotopyEquiv K) n).symm.trans
    (rationalZeroDifferentialDualEquiv (rationalHomologyComplex K) (fun _ _ => rfl) n)

#print axioms rationalHomologyDualEquiv
#print axioms rationalZeroDifferentialDualEquiv
#print axioms rationalDualCohomologyHomotopyEquiv
end HodgeLean.Foundations.Singular
