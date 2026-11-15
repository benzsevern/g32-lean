import HodgeLean.Foundations.SchurWeylLie

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations

/-- The top alternating tensor transforms by the determinant character under
any linear operator, including singular ones. The tensor is the existing
basis-normalized `SchurWeyl.detTensorDual`.
Source: Weyl, The Classical Groups, Chapter II, §9; Procesi, Lie Groups,
Chapter 11, §2 (the determinant generator). -/
theorem volume_tensor_character {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (u : Module.End ℂ V) :
    SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u (SchurWeyl.detTensorDual ℂ V) =
      u.det • SchurWeyl.detTensorDual ℂ V := by
  rw [SchurWeyl.detTensorDual_eq]
  let b := Module.finBasis ℂ V
  have hmap : SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u
      (SchurWeyl.antisymTensor ℂ V _ b) =
      SchurWeyl.antisymTensor ℂ V _ (fun i => u (b i)) := by
    simp only [SchurWeyl.antisymTensor_apply, map_sum, map_zsmul,
      SchurWeyl.tensorPow_tprod]
  rw [hmap]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro f
  have h := (f.compAlternatingMap (SchurWeyl.antisymTensor ℂ V
    (Fin (Module.finrank ℂ V)))).eq_smul_basis_det b
  have hh := congrArg (fun F => F (fun i => u (b i))) h
  simp only [LinearMap.compAlternatingMap_apply, AlternatingMap.smul_apply,
    smul_eq_mul] at hh
  have hdet : b.det (fun i => u (b i)) = u.det := by
    simpa only [Function.comp_def, b.det_self, mul_one] using b.det_comp u b
  rw [hdet] at hh
  rw [map_sub, map_smul, hh, smul_eq_mul, mul_comm, sub_self]

/-- The normalized determinant tensor is nonzero, including in dimension
zero. Hence the determinant sector cannot be removed by setting its
volume generator to zero.
Source: Weyl, The Classical Groups, Chapter II, §9; the normalization pairing
is `SchurWeyl.dualDistrib_detTensor_detTensorDual`. -/
theorem volume_tensor_ne_zero {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] : SchurWeyl.detTensorDual ℂ V ≠ 0 :=
  SchurWeyl.detTensorDual_ne_zero

end HodgeLean.Foundations.Abdulali
