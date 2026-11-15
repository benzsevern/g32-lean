import HodgeLean.Foundations.Curves.AbelTheorem.PeriodLinearAlgebra

noncomputable section
open HodgeLean.Foundations.Program
open Module
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {M : Type*} [AddCommGroup M] {g : ℕ}

theorem complex_tensor_right_coordinate (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (a c : Fin g → ℂ) (i : Fin g) :
    (b.baseChange ℂ).repr (complexLeftTensor b a + complexRightTensor b c) (.inr i) = c i := by
  classical
  simp [complexLeftTensor, complexRightTensor, Basis.baseChange_repr_tmul, Finsupp.single_apply]

theorem complex_tensor_conjugate (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (a c : Fin g → ℂ) :
    b2_conj M (complexLeftTensor b a + complexRightTensor b c) =
      complexLeftTensor b (fun i => star (a i)) + complexRightTensor b (fun i => star (c i)) := by
  rw [map_add, complex_left_tensor_conjugate]
  congr 1
  unfold complexRightTensor
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

end HodgeLean.Foundations.Curves.AbelTheorem
