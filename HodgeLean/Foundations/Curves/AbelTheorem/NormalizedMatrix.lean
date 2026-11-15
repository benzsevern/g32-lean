import HodgeLean.Foundations.Curves.AbelTheorem.TensorPairing
import Mathlib.LinearAlgebra.Dual.Basis

noncomputable section
open HodgeLean.Foundations.Program
open Module Set
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000
variable {M : Type*} [AddCommGroup M] {g : ℕ}
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def normalizedKernelTensor (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (P : (ℂ ⊗[ℤ] M) →ₗ[ℂ] Dual ℂ V) (forms : Basis (Fin g) ℂ V)
    (c : Fin g → ℂ) : ℂ ⊗[ℤ] M :=
  complexLeftTensor b (fun j => -∑ i, c i * P ((1 : ℂ) ⊗ₜ[ℤ] b (.inr i)) (forms j)) +
    complexRightTensor b c

theorem normalized_kernel_tensor_mem (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (P : (ℂ ⊗[ℤ] M) →ₗ[ℂ] Dual ℂ V) (forms : Basis (Fin g) ℂ V)
    (hn : ∀ i j, P ((1 : ℂ) ⊗ₜ[ℤ] b (.inl i)) (forms j) = if i = j then 1 else 0)
    (c : Fin g → ℂ) : normalizedKernelTensor b P forms c ∈ P.ker := by
  classical
  have htmul (r : ℂ) (ell : M) : P (r ⊗ₜ[ℤ] ell) = r • P ((1 : ℂ) ⊗ₜ[ℤ] ell) := by
    simpa only [TensorProduct.smul_tmul', smul_eq_mul, mul_one] using
      P.map_smul r ((1 : ℂ) ⊗ₜ[ℤ] ell)
  have hs (v : Fin g → M) (r : Fin g → ℂ) :
      P (∑ i, r i ⊗ₜ[ℤ] v i) = ∑ i, r i • P ((1 : ℂ) ⊗ₜ[ℤ] v i) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact htmul (r i) (v i)
  change P (normalizedKernelTensor b P forms c) = 0
  apply forms.ext
  intro j
  simp only [normalizedKernelTensor, complexLeftTensor, complexRightTensor,
    map_add, hs, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_eq_mul, hn, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, ite_true, LinearMap.zero_apply]
  ring

end HodgeLean.Foundations.Curves.AbelTheorem
