import HodgeLean.Foundations.Singular.RationalHomologyFinite
import HodgeLean.Foundations.Singular.FiniteTensorDual
import HodgeLean.Foundations.Singular.TensorDegreeSum

/-! The actual factorwise dual pairing in the rational tensor-cohomology equivalence. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open CategoryTheory
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The actual dual pairing for one finite-first-factor rational cohomology bidegree.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology tensor pairing. -/
def rationalTensorCohomologyFactorEquiv (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (a : tensorDegreeIndex n) [h : Module.Finite ℚ (K.sc a.1.1).linearDual.homology] :
    ((K.sc a.1.1).linearDual.homology ⊗[ℚ] (L.sc a.1.2).linearDual.homology) ≃ₗ[ℚ]
      Module.Dual ℚ (tensorDegreeFactor (rationalHomologyComplex K) (rationalHomologyComplex L) n a) := by
  letI : Module.Finite ℚ (rationalHomologyQuotient K a.1.1) := rationalHomologyQuotient_finite K a.1.1
  exact (TensorProduct.congr (rationalHomologyDualEquiv K a.1.1) (rationalHomologyDualEquiv L a.1.2)).trans
    (finiteRationalTensorDualEquiv (rationalHomologyQuotient K a.1.1) (rationalHomologyQuotient L a.1.2))

/-- The factorwise rational cohomology equivalence evaluates pure tensors by the product of factor functionals.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor evaluation pairing. -/
theorem rationalTensorCohomologyFactorEquiv_tmul (K L : ChainComplex (ModuleCat ℚ) ℕ) (n : ℕ)
    (a : tensorDegreeIndex n) [Module.Finite ℚ (K.sc a.1.1).linearDual.homology]
    (α : (K.sc a.1.1).linearDual.homology) (β : (L.sc a.1.2).linearDual.homology)
    (u : rationalHomologyQuotient K a.1.1) (v : rationalHomologyQuotient L a.1.2) :
    rationalTensorCohomologyFactorEquiv K L n a (α ⊗ₜ[ℚ] β) (u ⊗ₜ[ℚ] v) =
      rationalHomologyDualEquiv K a.1.1 α u * rationalHomologyDualEquiv L a.1.2 β v := by
  letI : Module.Finite ℚ (rationalHomologyQuotient K a.1.1) := rationalHomologyQuotient_finite K a.1.1
  change finiteRationalTensorDualEquiv (rationalHomologyQuotient K a.1.1) (rationalHomologyQuotient L a.1.2)
    (TensorProduct.congr (rationalHomologyDualEquiv K a.1.1) (rationalHomologyDualEquiv L a.1.2)
      (α ⊗ₜ[ℚ] β)) (u ⊗ₜ[ℚ] v) = _
  have ht := TensorProduct.congr_tmul (rationalHomologyDualEquiv K a.1.1)
    (rationalHomologyDualEquiv L a.1.2) α β
  rw [ht]
  exact finiteRationalTensorDualEquiv_tmul _ _
    (rationalHomologyDualEquiv K a.1.1 α) (rationalHomologyDualEquiv L a.1.2 β) u v

#print axioms rationalTensorCohomologyFactorEquiv_tmul
#print axioms rationalTensorCohomologyFactorEquiv
end HodgeLean.Foundations.Singular
