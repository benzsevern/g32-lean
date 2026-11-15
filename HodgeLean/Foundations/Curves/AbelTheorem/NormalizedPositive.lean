import HodgeLean.Foundations.Curves.AbelTheorem.NormalizedSymmetry
import HodgeLean.Foundations.Curves.AbelTheorem.TensorCoordinates
import HodgeLean.Foundations.Curves.AbelTheorem.QuadraticImaginary

noncomputable section
open HodgeLean.Foundations.Program
open Module Set
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {M : Type*} [AddCommGroup M] {g : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem normalized_matrix_positive (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (Q : LinearMap.BilinForm ℤ M)
    (P : (ℂ ⊗[ℤ] M) →ₗ[ℂ] Dual ℂ V) (forms : Basis (Fin g) ℂ V)
    (hR : b2_IsRiemannForm M P.ker Q)
    (hab : ∀ i j, Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0)
    (hbb : ∀ i j, Q (b (.inr i)) (b (.inr j)) = 0)
    (hn : ∀ i j, P ((1 : ℂ) ⊗ₜ[ℤ] b (.inl i)) (forms j) = if i = j then 1 else 0)
    (z : Fin g → ℂ) (hz : z ≠ 0) :
    0 < (∑ i, ∑ j, star (z i) * P ((1 : ℂ) ⊗ₜ[ℤ] b (.inr i)) (forms j) * z j).im := by
  let a : Fin g → ℂ := fun j => -∑ i, z i * P ((1 : ℂ) ⊗ₜ[ℤ] b (.inr i)) (forms j)
  let x := normalizedKernelTensor b P forms z
  have hx : x ≠ 0 := by
    intro he
    apply hz
    funext i
    calc
      z i = (b.baseChange ℂ).repr x (.inr i) := (complex_tensor_right_coordinate b a z i).symm
      _ = 0 := by rw [he, map_zero]; rfl
  have hp := hR.positive x (normalized_kernel_tensor_mem b P forms hn z) hx
  change 0 < (Complex.I * Q.baseChange ℂ
    (complexLeftTensor b a + complexRightTensor b z)
    (b2_conj M (complexLeftTensor b a + complexRightTensor b z))).re at hp
  rw [complex_tensor_conjugate, complex_symplectic_pairing b Q hR.alt hab haa hbb] at hp
  have hsym := normalized_matrix_symmetric b Q P forms hR hab haa hbb hn
  rw [symplectic_quadratic_imaginary _ hsym z] at hp
  linarith

end HodgeLean.Foundations.Curves.AbelTheorem
