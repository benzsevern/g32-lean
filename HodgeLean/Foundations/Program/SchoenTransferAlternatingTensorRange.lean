import HodgeLean.Foundations.Program.SchoenTransferAlternatingNormalization
import Mathlib.Data.Fintype.Perm

noncomputable section
open scoped BigOperators TensorProduct
namespace HodgeLean.Foundations.Program

/-- Evaluation commutes with multiplication by an integer unit. -/
theorem s4_linearMap_unit_apply {K P Q : Type*} [CommRing K]
    [AddCommGroup P] [Module K P] [AddCommGroup Q] [Module K Q]
    (u : ℤˣ) (f : P →ₗ[K] Q) (x : P) : (u • f) x = u • f x := by
  rcases Int.units_eq_one_or u with rfl | rfl <;>
    simp only [Units.smul_def, Units.val_one, Units.val_neg, one_smul,
      neg_one_smul, LinearMap.neg_apply]

/-- Permutation of the arguments of a pure ordered tensor.
Source: Schoen (1988), Remark 1.4, p. 6, ordered tensors. -/
def s4_tensorPermutation {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    (⨂[K] i : Fin n, M) →ₗ[K] (⨂[K] i : Fin n, M) :=
  PiTensorProduct.lift ((PiTensorProduct.tprod K).domDomCongr σ)

example {K M : Type*} [CommRing K] [AddCommGroup M] [Module K M]
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    s4_tensorPermutation (K := K) (M := M) n σ 0 = 0 := map_zero _

/-- Exterior projection followed by tensor alternation is the signed permutation sum. -/
theorem s4_tensor_alternation_projector {K M : Type*} [CommRing K]
    [AddCommGroup M] [Module K M] (n : ℕ) :
    (exteriorPower.toTensorPower K M n).comp
      (PiTensorProduct.lift (exteriorPower.ιMulti K n (M := M)).toMultilinearMap) =
      ∑ σ : Equiv.Perm (Fin n), σ.sign • s4_tensorPermutation (K := K) (M := M) n σ := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply, PiTensorProduct.lift.tprod,
    AlternatingMap.coe_multilinearMap, exteriorPower.toTensorPower_apply_ιMulti,
    LinearMap.sum_apply, s4_linearMap_unit_apply, s4_tensorPermutation,
    MultilinearMap.domDomCongr_apply]

/-- Every tensor with the alternating permutation law belongs to the exterior tensor image. -/
theorem s4_mem_tensor_alternation_range {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] (n : ℕ) (z : ⨂[K] i : Fin n, M)
    (hz : ∀ σ : Equiv.Perm (Fin n), s4_tensorPermutation n σ z = σ.sign • z) :
    z ∈ LinearMap.range (exteriorPower.toTensorPower K M n) := by
  have he := LinearMap.congr_fun (s4_tensor_alternation_projector (K := K) (M := M) n) z
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, s4_linearMap_unit_apply,
    hz, smul_smul, Int.units_mul_self, one_smul, Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin] at he
  have hc : (Nat.factorial n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  refine ⟨(Nat.factorial n : K)⁻¹ •
    PiTensorProduct.lift (exteriorPower.ιMulti K n (M := M)).toMultilinearMap z, ?_⟩
  rw [map_smul, he, ← Nat.cast_smul_eq_nsmul K, smul_smul, inv_mul_cancel₀ hc, one_smul]

end HodgeLean.Foundations.Program
