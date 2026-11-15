import HodgeLean.Foundations.Singular.TensorDegreeSum
import HodgeLean.Foundations.Singular.RationalTensorDual
import HodgeLean.Foundations.Singular.RationalDirectSumDual
import HodgeLean.Foundations.Singular.RationalHomologyFinite
import HodgeLean.Foundations.Singular.FiniteTensorDual
import HodgeLean.Foundations.Singular.RationalTensorFactor

/-! The algebraic rational tensor-cohomology comparison with one degreewise finite factor. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct DirectSum
namespace HodgeLean.Foundations.Singular

/-- The algebraic tensor-cohomology equivalence when actual dual cohomology of the first factor is finite.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology Künneth theorem. -/
def rationalTensorCohomologyEquiv (K L : ChainComplex (ModuleCat ℚ) ℕ)
    (hK : ∀ p : ℕ, Module.Finite ℚ (K.sc p).linearDual.homology) (n : ℕ) :
    (⨁ a : tensorDegreeIndex n,
      (K.sc a.1.1).linearDual.homology ⊗[ℚ] (L.sc a.1.2).linearDual.homology) ≃ₗ[ℚ]
      ((HomologicalComplex.tensorObj K L).sc n).linearDual.homology := by
  letI (p : ℕ) : Module.Finite ℚ (K.sc p).linearDual.homology := hK p
  exact (DirectSum.congrLinearEquiv (fun a : tensorDegreeIndex n =>
    rationalTensorCohomologyFactorEquiv K L n a)).trans
    ((rationalFiniteDirectSumDualEquiv
      (tensorDegreeFactor (rationalHomologyComplex K) (rationalHomologyComplex L) n)).symm.trans
      ((tensorDegreeSumEquiv (rationalHomologyComplex K) (rationalHomologyComplex L) n).dualMap.trans
        (rationalTensorDualHomologyEquiv K L n).symm))

#print axioms rationalTensorCohomologyEquiv
end HodgeLean.Foundations.Singular
