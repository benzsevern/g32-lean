import HodgeLean.Foundations.Singular.RationalHomologyEquivalence
import HodgeLean.Foundations.Singular.TensorHomotopy

/-! Tensor products of actual rational homology deformation equivalences. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
namespace HodgeLean.Foundations.Singular

/-- The actual total tensor complex retracts up to homotopy onto the tensor of its homology quotients.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient algebraic Künneth argument. -/
def rationalTensorHomologyHomotopyEquiv (K L : ChainComplex (ModuleCat ℚ) ℕ) :
    HomotopyEquiv (HomologicalComplex.tensorObj K L)
      (HomologicalComplex.tensorObj (rationalHomologyComplex K) (rationalHomologyComplex L)) :=
  tensorComplexHomotopyEquiv (rationalHomologyHomotopyEquiv K) (rationalHomologyHomotopyEquiv L)

#print axioms rationalTensorHomologyHomotopyEquiv
end HodgeLean.Foundations.Singular
