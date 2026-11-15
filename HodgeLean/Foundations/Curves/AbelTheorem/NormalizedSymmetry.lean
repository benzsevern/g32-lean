import HodgeLean.Foundations.Curves.AbelTheorem.NormalizedMatrix

noncomputable section
open HodgeLean.Foundations.Program
open Module Set
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {M : Type*} [AddCommGroup M] {g : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem normalized_matrix_symmetric (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (Q : LinearMap.BilinForm ℤ M)
    (P : (ℂ ⊗[ℤ] M) →ₗ[ℂ] Dual ℂ V) (forms : Basis (Fin g) ℂ V)
    (hR : b2_IsRiemannForm M P.ker Q)
    (hab : ∀ i j, Q (b (.inl i)) (b (.inr j)) = if i = j then 1 else 0)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0)
    (hbb : ∀ i j, Q (b (.inr i)) (b (.inr j)) = 0)
    (hn : ∀ i j, P ((1 : ℂ) ⊗ₜ[ℤ] b (.inl i)) (forms j) = if i = j then 1 else 0)
    (i j : Fin g) :
    P ((1 : ℂ) ⊗ₜ[ℤ] b (.inr i)) (forms j) =
      P ((1 : ℂ) ⊗ₜ[ℤ] b (.inr j)) (forms i) := by
  classical
  have hi := normalized_kernel_tensor_mem b P forms hn (Pi.single i (1 : ℂ))
  have hj := normalized_kernel_tensor_mem b P forms hn (Pi.single j (1 : ℂ))
  have he := hR.isotropic _ hi _ hj
  simp only [normalizedKernelTensor,
    complex_symplectic_pairing b Q hR.alt hab haa hbb] at he
  simp [Pi.single_apply, mul_ite, ite_mul] at he
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, ite_true] at he
  linear_combination -he

end HodgeLean.Foundations.Curves.AbelTheorem
