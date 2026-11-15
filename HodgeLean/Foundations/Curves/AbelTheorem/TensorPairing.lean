import HodgeLean.Foundations.Curves.AbelTheorem.PeriodLinearAlgebra

noncomputable section
open HodgeLean.Foundations.Program
open Module Set
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {M : Type*} [AddCommGroup M] {g : ℕ}

theorem complex_left_right_pairing (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (Q : LinearMap.BilinForm ℤ M)
    (hab : ∀ i j, Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0)
    (c d : Fin g → ℂ) :
    Q.baseChange ℂ (complexLeftTensor b c) (complexRightTensor b d) =
      ∑ i, c i * d i := by
  classical
  simp [complexLeftTensor, complexRightTensor, LinearMap.sum_apply,
    LinearMap.BilinForm.baseChange_tmul, hab, ite_smul]

theorem complex_symplectic_pairing (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (Q : LinearMap.BilinForm ℤ M) (hQ : ∀ x, Q x x = 0)
    (hab : ∀ i j, Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0)
    (hbb : ∀ i j, Q (b (.inr i)) (b (.inr j)) = 0)
    (a c a' c' : Fin g → ℂ) :
    Q.baseChange ℂ (complexLeftTensor b a + complexRightTensor b c)
      (complexLeftTensor b a' + complexRightTensor b c') =
      ∑ i, (a i * c' i - c i * a' i) := by
  have hll := complex_left_tensor_pairing_zero b Q haa a a'
  have hlr := complex_left_right_pairing b Q hab a c'
  have hrl : Q.baseChange ℂ (complexRightTensor b c) (complexLeftTensor b a') =
      -(∑ i, c i * a' i) := by
    rw [b2a_baseChange_skew Q hQ, complex_left_right_pairing b Q hab]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hrr : Q.baseChange ℂ (complexRightTensor b c) (complexRightTensor b c') = 0 := by
    simp only [complexRightTensor, map_sum, LinearMap.sum_apply,
      LinearMap.BilinForm.baseChange_tmul, hbb, zero_smul, Finset.sum_const_zero]
  simp only [map_add, LinearMap.add_apply, hll, hlr, hrl, hrr,
    zero_add, add_zero, Finset.sum_sub_distrib, sub_eq_add_neg]
  rw [Finset.sum_add_distrib, Finset.sum_neg_distrib]
  ring

end HodgeLean.Foundations.Curves.AbelTheorem
