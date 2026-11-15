import HodgeLean.Blocks.HodgeStructure.TensorProduct

/-! # Hodge classes -/

open scoped TensorProduct
noncomputable section
namespace HodgeBlocks

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [Module.Finite ℚ V]
  [AddCommGroup W] [Module ℚ W] [Module.Finite ℚ W]

/-- The canonical rational inclusion into the complexification. -/
def complexify (V : Type*) [AddCommGroup V] [Module ℚ V] : V →ₗ[ℚ] ℂ ⊗[ℚ] V :=
  TensorProduct.mk ℚ ℂ V 1

@[simp] theorem complexify_apply (v : V) : complexify V v = 1 ⊗ₜ[ℚ] v := rfl

/-- A rational vector is a Hodge class when its complexification has bidegree `(p,p)`. -/
def IsHodgeClass {p : ℤ} (M : QHodgeStructure (2 * p) V) (v : V) : Prop :=
  complexify V v ∈ M.H (p, p)

/-- Hodge classes in a direct sum are exactly pairs of Hodge classes. -/
theorem isHodgeClass_prod {p : ℤ} (M : QHodgeStructure (2 * p) V)
    (N : QHodgeStructure (2 * p) W) (v : V) (w : W) :
    IsHodgeClass (QHodgeStructure.prod V W M N) (v, w) ↔
      IsHodgeClass M v ∧ IsHodgeClass N w := by
  rw [IsHodgeClass, IsHodgeClass, IsHodgeClass]
  change (1 ⊗ₜ[ℚ] (v, w)) ∈ ((M.H (p, p)).prod (N.H (p, p))).map _ ↔ _
  rw [Submodule.mem_map_equiv]
  simp [prodBaseChange_tmul, Submodule.mem_prod]

/-- **HISTORICAL naming note (superseded by hodge-LEAN5, 2026-09-23):** this is only the
narrower fact that the tensor of two Hodge classes lands in the ad hoc span `tensorPiece`, which
is defined to contain exactly such products; it is close to a restatement of `tensorPiece`'s own
definition (`tmul_mem_tensorPiece`), not an independent derivation. **The genuine theorem is now
`isHodgeClass_tensor` below**, proved for the real tensor-product structure
`QHodgeStructure.tensorHodge` built in `TensorProduct.lean`. This narrow theorem and the ad hoc
`tensorPiece` it uses are kept, unchanged, as a separate, smaller object under its own name — not
superseded, just no longer the only tensor-related fact in this file. Originally referee-flagged
(hodge-LEAN1) as misleadingly named relative to "the tensor product of two Hodge classes is a
Hodge class"; that naming concern is resolved by `isHodgeClass_tensor` proving the real
statement under that name. -/
theorem isHodgeClass_tensor_mem_tensorPiece {p q : ℤ} (M : QHodgeStructure (2 * p) V)
    (N : QHodgeStructure (2 * q) W) {v : V} {w : W}
    (hv : IsHodgeClass M v) (hw : IsHodgeClass N w) :
    complexify (V ⊗[ℚ] W) (v ⊗ₜ[ℚ] w) ∈ tensorPiece M N (p, p) (q, q) := by
  exact tmul_mem_tensorPiece M N (p, p) (q, q) hv hw

theorem isHodgeClass_tensor {p q : ℤ} (M : QHodgeStructure (2 * p) V)
    (N : QHodgeStructure (2 * q) W) {v : V} {w : W}
    (hv : IsHodgeClass M v) (hw : IsHodgeClass N w) :
    IsHodgeClass (QHodgeStructure.tensorHodge M N) (v ⊗ₜ[ℚ] w) := by
  rw [IsHodgeClass]
  rw [QHodgeStructure.tensorHodge_H]
  rw [Submodule.mem_map_equiv]
  rw [complexify_apply]
  change tensorBaseChange (V := V) (W := W)
    (1 ⊗ₜ[ℚ] (v ⊗ₜ[ℚ] w)) ∈ tensorConvolutionPiece M N (p + q, p + q)
  rw [tensorBaseChange_tmul]
  rw [tensorConvolutionPiece]
  have ha : ((p, p), (q, q)) ∈ addBidegrees ⁻¹' {(p + q, p + q)} := by
    simp [addBidegrees]
  apply Submodule.mem_iSup_of_mem ((p, p), (q, q))
  apply Submodule.mem_iSup_of_mem ha
  exact ⟨⟨complexify V v, hv⟩ ⊗ₜ[ℂ] ⟨complexify W w, hw⟩, rfl⟩

/-- A morphism of Hodge structures sends Hodge classes to Hodge classes.
`LinearMap.baseChange_tmul` (`Mathlib/LinearAlgebra/TensorProduct/Tower.lean`) computes the
complexification of the rational linear map on a pure tensor. -/
theorem QHodgeStructure.Hom.map_isHodgeClass {p : ℤ}
    {M : QHodgeStructure (2 * p) V} {N : QHodgeStructure (2 * p) W}
    (f : M.Hom N) {v : V} (hv : IsHodgeClass M v) :
    IsHodgeClass N (f.toLinearMap v) := by
  apply f.maps_pieces (p, p)
  exact ⟨1 ⊗ₜ[ℚ] v, hv, by simp⟩

#print axioms isHodgeClass_prod
#print axioms isHodgeClass_tensor
#print axioms isHodgeClass_tensor_mem_tensorPiece
#print axioms QHodgeStructure.Hom.map_isHodgeClass

end HodgeBlocks
