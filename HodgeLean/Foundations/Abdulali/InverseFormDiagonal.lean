import HodgeLean.Foundations.Abdulali.InverseFormGenerators

noncomputable section
open scoped TensorProduct
open HodgeLean.Foundations HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Abdulali

/-- The standard inverse form is the diagonal sum of coordinate basis tensors. -/
theorem standardInverseFormTensor_diagonal (d : ℕ) :
    standardInverseFormTensor d =
      ∑ i : Fin d, PiTensorProduct.tprod ℂ (fun _ : Fin 2 => (Pi.single i 1 : Fin d → ℂ)) := by
  classical
  unfold standardInverseFormTensor
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_eq_single i]
  · congr 1
    funext s
    fin_cases s <;> simp [m1b_matrixPairVectors]
  · intro j _ hji
    apply (PiTensorProduct.tprod ℂ).map_coord_zero (0 : Fin 2)
    simp [m1b_matrixPairVectors, Matrix.one_apply, Ne.symm hji]
  · intro hi
    exact False.elim (hi (Finset.mem_univ _))

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- The coordinate basis transported through the symmetric standard coordinates. -/
def inverseFormBasis (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V :=
  (Pi.basisFun ℂ (Fin (Module.finrank ℂ V))).map
    (Classical.choose (m1b_symmetric_standard_coordinates B hB hs)).symm

/-- The inverse form is diagonal in the transported coordinate basis. -/
theorem inverseFormTensor_diagonal (B : LinearMap.BilinForm ℂ V) (hB : B.Nondegenerate)
    (hs : ∀ x y, B x y = B y x) :
    inverseFormTensor B hB hs =
      ∑ i : Fin (Module.finrank ℂ V),
        PiTensorProduct.tprod ℂ (fun _ : Fin 2 => inverseFormBasis B hB hs i) := by
  rw [inverseFormTensor, standardInverseFormTensor_diagonal, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [m1b_tensorEquiv, PiTensorProduct.congr_tprod, inverseFormBasis,
    Module.Basis.map_apply, Pi.basisFun_apply]

end HodgeLean.Foundations.Abdulali
