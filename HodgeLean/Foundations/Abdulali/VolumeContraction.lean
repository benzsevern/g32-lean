import HodgeLean.Foundations.Abdulali.SpecialOrthogonalFFT
import HodgeLean.Foundations.Abdulali.DeterminantSectorLift
import HodgeLean.Foundations.Abdulali.VolumeTwist

noncomputable section
open scoped TensorProduct
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations

/-- Contraction of the final top-degree block against the dual volume tensor,
normalized by `d!`. The slot order is the existing `tensorAppend` order.
Source: Weyl, The Classical Groups, Chapter II, §9; Procesi, Lie Groups,
Chapter 11, §2. -/
def normalizedVolumeContraction {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (n : ℕ) :
    (⨂[ℂ]^(n + Module.finrank ℂ V) V) →ₗ[ℂ] (⨂[ℂ]^n V) :=
  (((Module.finrank ℂ V).factorial : ℂ)⁻¹ •
    ((TensorProduct.rid ℂ (⨂[ℂ]^n V)).toLinearMap.comp
      ((PiTensorProduct.dualDistrib (SchurWeyl.detTensor ℂ V)).lTensor (⨂[ℂ]^n V)))).comp
    (InvariantsExterior.tensorAppend n (Module.finrank ℂ V)).symm.toLinearMap

example {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (n : ℕ) : normalizedVolumeContraction (V := V) n 0 = 0 := map_zero _

/-- Appending the normalized volume and contracting it returns the original
tensor with coefficient one, including dimension zero.
Source: Weyl, The Classical Groups, Chapter II, §9; the actual pairing is
`SchurWeyl.dualDistrib_detTensor_detTensorDual`. -/
theorem normalizedVolumeContraction_append {V : Type*} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (n : ℕ) (t : ⨂[ℂ]^n V) :
    normalizedVolumeContraction n (InvariantsExterior.tensorAppend n (Module.finrank ℂ V)
      (t ⊗ₜ[ℂ] SchurWeyl.detTensorDual ℂ V)) = t := by
  have hf : ((Module.finrank ℂ V).factorial : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (Module.finrank ℂ V)
  simp [normalizedVolumeContraction, SchurWeyl.dualDistrib_detTensor_detTensorDual,
    smul_smul, hf]

end HodgeLean.Foundations.Abdulali

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The dual top alternating tensor also transforms by the determinant under transpose.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, top exterior powers. -/
theorem tensorPow_dual_volume (u : Module.End ℂ V) :
    SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u.dualMap
      (SchurWeyl.detTensor ℂ V) = LinearMap.det u • SchurWeyl.detTensor ℂ V := by
  classical
  let b := (Module.finBasis ℂ V).dualBasis
  have hm : SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u.dualMap
      (SchurWeyl.antisymTensor ℂ (Module.Dual ℂ V) _ b) =
      SchurWeyl.antisymTensor ℂ (Module.Dual ℂ V) _ (u.dualMap ∘ b) := by
    simp only [SchurWeyl.antisymTensor_apply, map_sum, map_zsmul,
      SchurWeyl.tensorPow_tprod, Function.comp_apply]
  rw [SchurWeyl.detTensor_eq, hm]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  have hh := (ℓ.compAlternatingMap
    (SchurWeyl.antisymTensor ℂ (Module.Dual ℂ V) _)).eq_smul_basis_det b
  have h := congr($hh (u.dualMap ∘ b))
  simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul,
    Module.Basis.det_comp, Module.Basis.det_self, mul_one, LinearMap.det_dualMap] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

/-- A top alternating covector normalized to take value one on the chosen volume tensor.
Source: Weyl, The Classical Groups, Chapter II, §17, contraction with the determinant
covector; antisymmetrization contributes the factorial normalization. -/
def normalizedVolumeCovector : (⨂[ℂ]^(Module.finrank ℂ V) V) →ₗ[ℂ] ℂ :=
  ((Module.finrank ℂ V).factorial : ℂ)⁻¹ •
    PiTensorProduct.dualDistrib (SchurWeyl.detTensor ℂ V)

/-- The determinant contraction retains coefficient one, also in dimension zero.
Source: Weyl, The Classical Groups, Chapter II, §17, determinant contraction. -/
theorem normalizedVolumeCovector_volume :
    normalizedVolumeCovector (SchurWeyl.detTensorDual ℂ V) = 1 := by
  rw [normalizedVolumeCovector, LinearMap.smul_apply,
    SchurWeyl.dualDistrib_detTensor_detTensorDual, smul_eq_mul]
  exact inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))

/-- Naturality of tensor evaluation under an endomorphism and its transpose.
Source: Weyl, The Classical Groups, Chapter II, §17, tensor contraction. -/
theorem tensor_evaluation_transpose (n : ℕ) (u : Module.End ℂ V)
    (t : ⨂[ℂ]^n (Module.Dual ℂ V)) (z : ⨂[ℂ]^n V) :
    PiTensorProduct.dualDistrib t (SchurWeyl.tensorPow (Fin n) u z) =
      PiTensorProduct.dualDistrib (SchurWeyl.tensorPow (Fin n) u.dualMap t) z := by
  induction t using PiTensorProduct.induction_on with
  | smul_tprod c f =>
    induction z using PiTensorProduct.induction_on with
    | smul_tprod d v =>
      simp only [map_smul, LinearMap.smul_apply, SchurWeyl.tensorPow_tprod,
        PiTensorProduct.dualDistrib_apply, LinearMap.dualMap_apply]
    | add x y hx hy =>
      simp only [map_add, hx, hy]
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, hx, hy]

/-- The normalized determinant covector is a determinant-character covector.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, determinant contraction. -/
theorem normalizedVolumeCovector_tensorPow (u : Module.End ℂ V)
    (z : ⨂[ℂ]^(Module.finrank ℂ V) V) :
    normalizedVolumeCovector (SchurWeyl.tensorPow (Fin (Module.finrank ℂ V)) u z) =
      LinearMap.det u * normalizedVolumeCovector z := by
  simp only [normalizedVolumeCovector, LinearMap.smul_apply]
  rw [tensor_evaluation_transpose, tensorPow_dual_volume, map_smul, LinearMap.smul_apply]
  simp only [smul_eq_mul]
  ring

/-- The base tensor representation, with no additional copy index.
Source: Weyl, The Classical Groups, Chapter II, §17, tensor representations. -/
def orthogonalBaseTensorRepresentation (B : LinearMap.BilinForm ℂ V) (n : ℕ) :
    orthogonalUnits B →* Module.End ℂ (⨂[ℂ]^n V) where
  toFun u := SchurWeyl.tensorPow (Fin n) u.val.val
  map_one' := SchurWeyl.tensorPow_one
  map_mul' u v := SchurWeyl.tensorPow_mul u.val.val v.val.val

/-- The determinant sector on repeated copies is the contraction of full orthogonal
fixed tensors with a normalized top alternating covector on one extra tensor factor.
Source: Weyl, The Classical Groups, Chapter II, §§9 and 17, adjoining a determinant
factor to change the determinant character to the trivial character. -/
theorem orthogonal_determinant_sector_eq_contracted_fixed
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate) (r n : ℕ) :
    let C : (⨂[ℂ]^n (Fin r → V)) ⊗[ℂ] (⨂[ℂ]^(Module.finrank ℂ V) V) →ₗ[ℂ]
        (⨂[ℂ]^n (Fin r → V)) :=
      (TensorProduct.rid ℂ _).toLinearMap.comp
        (TensorProduct.map LinearMap.id normalizedVolumeCovector)
    (⨅ g : orthogonalUnits B,
      LinearMap.ker (TensorProduct.map (orthogonalTensorRepresentation B r n g)
        (orthogonalBaseTensorRepresentation B (Module.finrank ℂ V) g) - LinearMap.id)).map C =
    ⨅ g : orthogonalUnits B,
      LinearMap.ker (orthogonalTensorRepresentation B r n g -
        orthogonalDeterminant B g • LinearMap.id) := by
  refine sign_sector_eq_contracted_fixed
    (orthogonalTensorRepresentation B r n)
    (orthogonalBaseTensorRepresentation B (Module.finrank ℂ V))
    (orthogonalDeterminant B) ?_ (SchurWeyl.detTensorDual ℂ V)
    normalizedVolumeCovector normalizedVolumeCovector_volume ?_ ?_
  · intro g
    rcases orthogonalDeterminant_sign B hB g with h | h <;> rw [h] <;> norm_num
  · intro g
    exact tensorPow_volume g.val.val
  · intro g d
    exact normalizedVolumeCovector_tensorPow g.val.val d

end HodgeLean.Foundations.Abdulali
