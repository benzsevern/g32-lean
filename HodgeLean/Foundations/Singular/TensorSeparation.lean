import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! Rational tensor vectors detected by products of scalar linear functionals. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
open scoped TensorProduct
namespace HodgeLean.Foundations.Singular

/-- The scalar product functional associated to two rational cochains.
Source: Hatcher, Algebraic Topology, §3.2, the tensor evaluation pairing. -/
def tensorScalarPairing
    {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (φ : V →ₗ[ℚ] ℚ) (ψ : W →ₗ[ℚ] ℚ) : V ⊗[ℚ] W →ₗ[ℚ] ℚ :=
  TensorProduct.lift (φ.smulRight ψ)

/-- Evaluation of the scalar tensor pairing on a pure tensor.
Source: Hatcher, Algebraic Topology, §3.2, the tensor evaluation pairing. -/
theorem tensorScalarPairing_tmul
    {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (φ : V →ₗ[ℚ] ℚ) (ψ : W →ₗ[ℚ] ℚ) (v : V) (w : W) :
    tensorScalarPairing φ ψ (v ⊗ₜ[ℚ] w) = φ v * ψ w := by
  simp only [tensorScalarPairing, TensorProduct.lift.tmul,
    LinearMap.smulRight_apply, LinearMap.smul_apply, smul_eq_mul]

/-- Products of rational linear functionals detect every tensor vector, without a dimension restriction.
Source: Hatcher, Algebraic Topology, §3.2, tensor bases over a field. -/
theorem tensorScalarPairings_separate
    {V W : Type} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    (z : V ⊗[ℚ] W)
    (hz : ∀ (φ : V →ₗ[ℚ] ℚ) (ψ : W →ₗ[ℚ] ℚ), tensorScalarPairing φ ψ z = 0) : z = 0 := by
  let b := Module.Basis.ofVectorSpace ℚ V
  let c := Module.Basis.ofVectorSpace ℚ W
  apply (b.tensorProduct c).repr.injective
  rw [map_zero]
  apply Finsupp.ext
  intro ij
  change (b.tensorProduct c).coord ij z = 0
  have he : (b.tensorProduct c).coord ij = tensorScalarPairing (b.coord ij.1) (c.coord ij.2) := by
    apply TensorProduct.ext'
    intro v w
    change (b.tensorProduct c).repr (v ⊗ₜ[ℚ] w) ij =
      tensorScalarPairing (b.coord ij.1) (c.coord ij.2) (v ⊗ₜ[ℚ] w)
    rcases ij with ⟨i, j⟩
    rw [Module.Basis.tensorProduct_repr_tmul_apply, tensorScalarPairing_tmul]
    exact mul_comm _ _
  rw [he]
  exact hz _ _

/-- Scalar tensor evaluation commutes with maps on its two factors.
Source: Hatcher, Algebraic Topology, §3.2, naturality of the tensor evaluation pairing. -/
theorem tensorScalarPairing_map
    {V W V' W' : Type}
    [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
    [AddCommGroup V'] [Module ℚ V'] [AddCommGroup W'] [Module ℚ W']
    (f : V →ₗ[ℚ] V') (g : W →ₗ[ℚ] W')
    (φ : V' →ₗ[ℚ] ℚ) (ψ : W' →ₗ[ℚ] ℚ) :
    (tensorScalarPairing φ ψ).comp (TensorProduct.map f g) =
      tensorScalarPairing (φ.comp f) (ψ.comp g) := by
  apply TensorProduct.ext'
  intro v w
  simp only [LinearMap.comp_apply, TensorProduct.map_tmul, tensorScalarPairing_tmul]

#print axioms tensorScalarPairing_map
#print axioms tensorScalarPairings_separate
#print axioms tensorScalarPairing
#print axioms tensorScalarPairing_tmul
end HodgeLean.Foundations.Singular
