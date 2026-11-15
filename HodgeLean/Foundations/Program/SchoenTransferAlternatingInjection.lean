import HodgeLean.Foundations.Program.SchoenTransferAlternatingNormalization
import Mathlib.LinearAlgebra.Charpoly.Basic

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Tensor alternation is injective over a field of characteristic zero. -/
theorem tensor_alternation_injective {K M : Type*} [Field K] [CharZero K]
    [AddCommGroup M] [Module K M] (n : ℕ) :
    Function.Injective (exteriorPower.toTensorPower K M n) := by
  let W := PiTensorProduct.lift (exteriorPower.ιMulti K n (M := M)).toMultilinearMap
  have hw : W.comp (exteriorPower.toTensorPower K M n) =
      (Nat.factorial n) • (LinearMap.id : (⋀[K]^n M) →ₗ[K] ⋀[K]^n M) := by
    rw [tensor_alternation_factorial, exteriorPower.alternatingMapLinearEquiv_ιMulti]
  intro x y hxy
  have he := congrArg W hxy
  change (W.comp (exteriorPower.toTensorPower K M n)) x =
    (W.comp (exteriorPower.toTensorPower K M n)) y at he
  rw [hw] at he
  have hc : (Nat.factorial n : K) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)
  have he' : (Nat.factorial n : K) • x = (Nat.factorial n : K) • y := by
    simpa only [LinearMap.smul_apply, LinearMap.id_apply, Nat.cast_smul_eq_nsmul] using he
  exact (smul_right_injective _ hc) he'

end HodgeLean.Foundations.Program
