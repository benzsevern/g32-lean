import HodgeLean.Foundations.Abdulali.LabelledQuadratics
import HodgeLean.Foundations.Program.MilneTensorSymmetricStandardCoordinates

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali
variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Transport of the standard inverse-form tensor along orthonormal coordinates.
Source: Weyl, The Classical Groups, Chapter II, §9, inverse-form contractions. -/
def inverseFormTensor (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) : ⨂[ℂ]^2 V :=
  m1b_tensorEquiv (Classical.choose (m1b_symmetric_standard_coordinates B hB hs)).symm 2
    (standardInverseFormTensor (Module.finrank ℂ V))

/-- An inverse-form tensor with independent labels on its two standard copies.
Source: Weyl, The Classical Groups, Chapter II, §9, polarized contractions. -/
def labeledInverseForm (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r : ℕ) (a : Fin 2 → Fin r) :
    ⨂[ℂ]^2 (Fin r → V) :=
  m1b_copyTensorIn r 2 a (inverseFormTensor B hB hs)

/-- Inverse-form tensors span all quadratic invariants, including dimension zero.
Source: Weyl, The Classical Groups, Chapter II, §9; transport of the coordinate
reflection calculation and decomposition into independent copy labels. -/
theorem orthogonal_quadratics_eq_inverseForm_span
    (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) (r : ℕ) :
    m1b_fixed (m1b_copies r '' m1b_isometries B) 2 =
      Submodule.span ℂ (Set.range (labeledInverseForm B hB hs r)) := by
  classical
  let e := Classical.choose (m1b_symmetric_standard_coordinates B hB hs)
  have he := Classical.choose_spec (m1b_symmetric_standard_coordinates B hB hs)
  let E := m1b_tensorEquiv (m1b_copiesEquiv e r) 2
  have hf : (m1b_fixed (m1b_copies r '' m1b_isometries B) 2).map E.toLinearMap =
      m1b_fixed (m1b_copies r '' m1b_isometries
        (1 : Matrix (Fin (Module.finrank ℂ V)) (Fin (Module.finrank ℂ V)) ℂ).toBilin') 2 := by
    rw [m1b_fixed_map, m1b_copies_isometries_conj, he]
  have ht (a : Fin 2 → Fin r) :
      E (labeledInverseForm B hB hs r a) =
        labelledInverseFormTensor (Module.finrank ℂ V) r a := by
    have hc : E.toLinearMap.comp (m1b_copyTensorIn r 2 a) =
        (m1b_copyTensorIn r 2 a).comp (m1b_tensorEquiv e 2).toLinearMap := by
      ext v
      simp only [E, m1b_tensorEquiv, m1b_copiesEquiv, m1b_copyTensorIn,
        LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
        LinearEquiv.coe_coe, PiTensorProduct.congr_tprod,
        PiTensorProduct.map_tprod, LinearMap.single_apply]
      congr 1
      funext i j
      change e ((Pi.single (a i) (v i) : Fin r → V) j) =
        (Pi.single (a i) (e (v i)) : Fin r → (Fin (Module.finrank ℂ V) → ℂ)) j
      simp only [Pi.single_apply]
      split_ifs <;> simp only [map_zero]
    change E (m1b_copyTensorIn r 2 a
      (m1b_tensorEquiv e.symm 2 (standardInverseFormTensor _))) = _
    have hh := LinearMap.congr_fun hc
      (m1b_tensorEquiv e.symm 2 (standardInverseFormTensor (Module.finrank ℂ V)))
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hh
    rw [hh, m1b_tensorEquiv_symm, LinearEquiv.apply_symm_apply]
    rfl
  apply Submodule.map_injective_of_injective E.injective
  rw [hf, Submodule.map_span, ← Set.range_comp]
  simp only [Function.comp_def, LinearEquiv.coe_coe, ht]
  by_cases hd : 0 < Module.finrank ℂ V
  · exact standard_orthogonal_labelled_quadratics _ hd r
  · have hz : Module.finrank ℂ V = 0 := Nat.eq_zero_of_not_pos hd
    haveI : Subsingleton (Fin (Module.finrank ℂ V) → ℂ) := by
      rw [hz]
      infer_instance
    apply le_antisymm
    · intro t _
      rw [m1b_tensor_zero_of_subsingleton 1 t]
      exact Submodule.zero_mem _
    · intro t _
      rw [m1b_tensor_zero_of_subsingleton 1 t]
      exact Submodule.zero_mem _

end HodgeLean.Foundations.Abdulali
