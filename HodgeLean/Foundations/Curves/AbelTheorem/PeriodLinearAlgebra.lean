import HodgeLean.Foundations.Curves.AbelTheorem.SymplecticBasis
import HodgeLean.Foundations.Program.RelativeTorusAlg
import Mathlib.LinearAlgebra.TensorProduct.Basis

noncomputable section
open Module Set
open HodgeLean.Foundations.Program
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Curves.AbelTheorem
set_option maxHeartbeats 400000

variable {M : Type*} [AddCommGroup M] {g : ℕ}

def complexLeftTensor (b : Basis (Fin g ⊕ Fin g) ℤ M) (c : Fin g → ℂ) :
    ℂ ⊗[ℤ] M := ∑ i, c i ⊗ₜ[ℤ] b (.inl i)

def complexRightTensor (b : Basis (Fin g ⊕ Fin g) ℤ M) (c : Fin g → ℂ) :
    ℂ ⊗[ℤ] M := ∑ i, c i ⊗ₜ[ℤ] b (.inr i)

theorem complex_left_tensor_coordinate (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (c : Fin g → ℂ) (i : Fin g) :
    (b.baseChange ℂ).repr (complexLeftTensor b c) (.inl i) = c i := by
  classical
  simp [complexLeftTensor, Basis.baseChange_repr_tmul, Finsupp.single_apply]

theorem complex_left_tensor_conjugate (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (c : Fin g → ℂ) :
    b2_conj M (complexLeftTensor b c) = complexLeftTensor b (fun i => star (c i)) := by
  unfold complexLeftTensor
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

theorem complex_left_tensor_pairing_zero (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (Q : LinearMap.BilinForm ℤ M)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0)
    (c d : Fin g → ℂ) :
    Q.baseChange ℂ (complexLeftTensor b c) (complexLeftTensor b d) = 0 := by
  simp only [complexLeftTensor, map_sum, LinearMap.sum_apply,
    LinearMap.BilinForm.baseChange_tmul, haa, zero_smul, Finset.sum_const_zero]

theorem complex_left_tensor_coefficients_zero (b : Basis (Fin g ⊕ Fin g) ℤ M)
    (Q : LinearMap.BilinForm ℤ M) (F : Submodule ℂ (ℂ ⊗[ℤ] M))
    (hR : b2_IsRiemannForm M F Q)
    (haa : ∀ i j, Q (b (.inl i)) (b (.inl j)) = 0)
    (c : Fin g → ℂ) (hc : complexLeftTensor b c ∈ F) : c = 0 := by
  have hv : complexLeftTensor b c = 0 := by
    by_contra hv
    have hp := hR.positive (complexLeftTensor b c) hc hv
    rw [complex_left_tensor_conjugate,
      complex_left_tensor_pairing_zero b Q haa] at hp
    norm_num at hp
  funext i
  calc
    c i = (b.baseChange ℂ).repr (complexLeftTensor b c) (.inl i) :=
      (complex_left_tensor_coordinate b c i).symm
    _ = 0 := by rw [hv, map_zero]; rfl

end HodgeLean.Foundations.Curves.AbelTheorem
