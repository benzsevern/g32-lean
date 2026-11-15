import HodgeLean.Foundations.Singular.TensorSeparation
import Mathlib.LinearAlgebra.Contraction

/-! The canonical tensor-dual equivalence with a finite-dimensional rational factor. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The canonical rational tensor-dual equivalence when the first factor is finite-dimensional.
Source: Hatcher, Algebraic Topology, §3.2, the field-coefficient cohomology Künneth pairing. -/
def finiteRationalTensorDualEquiv
    (V W : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [Module.Finite ℚ V] :
    (Module.Dual ℚ V ⊗[ℚ] Module.Dual ℚ W) ≃ₗ[ℚ] Module.Dual ℚ (V ⊗[ℚ] W) :=
  (dualTensorHomEquiv ℚ V (Module.Dual ℚ W)).trans (TensorProduct.lift.equiv (RingHom.id ℚ) V W ℚ)

/-- The finite tensor-dual equivalence has the specified product evaluation on pure tensors.
Source: Hatcher, Algebraic Topology, §3.2, the cohomology tensor pairing. -/
theorem finiteRationalTensorDualEquiv_tmul
    (V W : Type) [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [Module.Finite ℚ V] (φ : Module.Dual ℚ V) (ψ : Module.Dual ℚ W) (v : V) (w : W) :
    finiteRationalTensorDualEquiv V W (φ ⊗ₜ[ℚ] ψ) (v ⊗ₜ[ℚ] w) = φ v * ψ w := by
  simp only [finiteRationalTensorDualEquiv, LinearEquiv.trans_apply,
    TensorProduct.lift.equiv_apply, dualTensorHomEquiv_tmul, LinearMap.smul_apply, smul_eq_mul]

#print axioms finiteRationalTensorDualEquiv_tmul
#print axioms finiteRationalTensorDualEquiv
end HodgeLean.Foundations.Singular
