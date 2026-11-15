import HodgeLean.Foundations.Abdulali.VolumeContraction
import Mathlib.LinearAlgebra.Coevaluation

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- Contracting coevaluation recovers the covector transported by any linear map. -/
theorem transported_coevaluation_contract
    {U W : Type*} [AddCommGroup U] [Module ℂ U] [FiniteDimensional ℂ U]
    [AddCommGroup W] [Module ℂ W]
    (F : Module.Dual ℂ U →ₗ[ℂ] W) (ℓ : Module.Dual ℂ U) :
    (TensorProduct.rid ℂ W) (TensorProduct.map F ℓ
      ((TensorProduct.comm ℂ U (Module.Dual ℂ U)) (coevaluation ℂ U 1))) = F ℓ := by
  classical
  simp only [coevaluation_apply_one, map_sum, TensorProduct.comm_tmul,
    TensorProduct.map_tmul, TensorProduct.rid_tmul]
  simp_rw [← map_smul]
  rw [← map_sum]
  congr 1
  simpa only [Module.Basis.dualBasis_repr, Module.Basis.coe_dualBasis,
    Module.Basis.coord_apply] using (Module.Basis.ofVectorSpace ℂ U).dualBasis.sum_repr ℓ

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The fully transverse pairing tensor associated to a map from covectors to vectors. -/
def transverseTensor (d : ℕ) (T : Module.Dual ℂ V →ₗ[ℂ] V) :
    (⨂[ℂ]^d V) ⊗[ℂ] (⨂[ℂ]^d V) :=
  TensorProduct.map
    ((PiTensorProduct.map (fun _ : Fin d => T)).comp
      PiTensorProduct.dualDistribEquiv.symm.toLinearMap) LinearMap.id
    ((TensorProduct.comm ℂ _ _) (coevaluation ℂ (⨂[ℂ]^d V) 1))

/-- Contracting all transverse pairs transports the determinant covector, with its exact scale. -/
theorem transverseTensor_volume_contract (T : Module.Dual ℂ V →ₗ[ℂ] V) :
    (TensorProduct.rid ℂ _) (TensorProduct.map LinearMap.id normalizedVolumeCovector
      (transverseTensor (Module.finrank ℂ V) T)) =
    ((Module.finrank ℂ V).factorial : ℂ)⁻¹ •
      PiTensorProduct.map (fun _ : Fin (Module.finrank ℂ V) => T)
        (SchurWeyl.detTensor ℂ V) := by
  let F := (PiTensorProduct.map (fun _ : Fin (Module.finrank ℂ V) => T)).comp
    PiTensorProduct.dualDistribEquiv.symm.toLinearMap
  have hmap : (TensorProduct.map (LinearMap.id : (⨂[ℂ]^(Module.finrank ℂ V) V) →ₗ[ℂ] _)
      (normalizedVolumeCovector (V := V))).comp (TensorProduct.map F LinearMap.id) =
      TensorProduct.map F normalizedVolumeCovector := by
    apply TensorProduct.ext'
    intro a b
    rfl
  change (TensorProduct.rid ℂ _) ((TensorProduct.map LinearMap.id normalizedVolumeCovector)
    (TensorProduct.map F LinearMap.id _)) = _
  rw [← LinearMap.comp_apply, hmap, transported_coevaluation_contract]
  change PiTensorProduct.map _ (PiTensorProduct.dualDistribEquiv.symm
    (normalizedVolumeCovector (V := V))) = _
  have hv : normalizedVolumeCovector (V := V) =
      PiTensorProduct.dualDistribEquiv
        (((Module.finrank ℂ V).factorial : ℂ)⁻¹ • SchurWeyl.detTensor ℂ V) := by
    rw [map_smul]
    rfl
  rw [hv, LinearEquiv.symm_apply_apply, map_smul]

/-- Transport of a top alternating covector tensor is a scalar multiple of the chosen volume. -/
theorem tensorMap_detTensor (T : Module.Dual ℂ V →ₗ[ℂ] V) :
    PiTensorProduct.map (fun _ : Fin (Module.finrank ℂ V) => T)
        (SchurWeyl.detTensor ℂ V) =
      (Module.finBasis ℂ V).det (T ∘ (Module.finBasis ℂ V).dualBasis) •
        SchurWeyl.detTensorDual ℂ V := by
  classical
  have hm : PiTensorProduct.map (fun _ : Fin (Module.finrank ℂ V) => T)
      (SchurWeyl.antisymTensor ℂ (Module.Dual ℂ V) _ (Module.finBasis ℂ V).dualBasis) =
      SchurWeyl.antisymTensor ℂ V _ (T ∘ (Module.finBasis ℂ V).dualBasis) := by
    simp only [SchurWeyl.antisymTensor_apply, map_sum, map_zsmul,
      PiTensorProduct.map_tprod, Function.comp_apply]
  rw [SchurWeyl.detTensor_eq, hm, SchurWeyl.detTensorDual_eq]
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro ℓ
  have hh := (ℓ.compAlternatingMap (SchurWeyl.antisymTensor ℂ V _)).eq_smul_basis_det
    (Module.finBasis ℂ V)
  have h := congr($hh (T ∘ (Module.finBasis ℂ V).dualBasis))
  simp only [LinearMap.compAlternatingMap_apply, smul_apply, smul_eq_mul] at h
  rw [map_sub, map_smul, h, smul_eq_mul, mul_comm, sub_self]

end HodgeLean.Foundations.Abdulali
