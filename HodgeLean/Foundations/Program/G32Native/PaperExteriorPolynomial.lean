import HodgeLean.Foundations.InvariantsExterior
import HodgeLean.Foundations.Program.G32Native.PaperAdditivePolynomialComparison

noncomputable section
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.InvariantsExterior HodgeLean.Foundations.SchurWeyl
open PiTensorProduct
open scoped TensorProduct

variable {K M : Type*} [Field K] [CharZero K] [AddCommGroup M] [Module K M]

/-- Taking the exterior quotient commutes with the tensor power of a linear map. -/
theorem paperExterior_wedgeQuotient_tensorPow (k : ℕ) (f : Module.End K M)
    (v : ⨂[K]^k M) :
    wedgeQuotient k (tensorPow (Fin k) f v) =
      exteriorPower.map k f (wedgeQuotient k v) := by
  induction v using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul, tensorPow_tprod, wedgeQuotient_tprod,
      exteriorPower.map_apply_ιMulti, Function.comp_def]
  | add x y hx hy => simp only [map_add, hx, hy]

/-- Exterior powers of a linear pencil have polynomial coordinates and the
linear coefficient is the exterior derivation. -/
theorem paperExterior_exists_polynomial_one_add_smul
    (k : ℕ) (N : Module.End K M) (v : ⋀[K]^k M)
    (ℓ : Module.Dual K (⋀[K]^k M)) :
    ∃ p : Polynomial K,
      (∀ t, p.eval t = ℓ (exteriorPower.map k (1 + t • N) v)) ∧
      p.coeff 1 = ℓ (exteriorDer k N v) := by
  let Λ : Module.End K (⨂[K]^k M) →ₗ[K] K :=
    (k.factorial : K)⁻¹ •
      (ℓ ∘ₗ wedgeQuotient k ∘ₗ LinearMap.applyₗ (exteriorPower.toTensorPower K M k v))
  obtain ⟨p, hp, hp1⟩ := exists_polynomial_tensorPow_one_add_smul Λ N
  refine ⟨p, fun t => ?_, ?_⟩
  · rw [hp]
    change (k.factorial : K)⁻¹ * ℓ (wedgeQuotient k
      (tensorPow (Fin k) (1 + t • N) (exteriorPower.toTensorPower K M k v))) = _
    rw [paperExterior_wedgeQuotient_tensorPow, wedgeQuotient_toTensorPower,
      map_smul, map_smul, smul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)), one_mul]
  · rw [hp1]
    change _ = ℓ ((k.factorial : K)⁻¹ • wedgeQuotient k
      (tensorDer (Fin k) N (exteriorPower.toTensorPower K M k v)))
    rw [map_smul]
    rfl

/-- On an exterior power, a square-zero one-parameter action fixes precisely the
vectors killed by the corresponding exterior derivation. -/
theorem paperExterior_square_zero_fixed_iff
    (k : ℕ) (N : Module.End K M) (hN : N * N = 0) (v : ⋀[K]^k M) :
    (∀ t : K, exteriorPower.map k (1 + t • N) v = v) ↔ exteriorDer k N v = 0 := by
  refine paperAdditivePolynomial_fixed_iff (K := K) (V := ⋀[K]^k M)
      (fun (t : K) => exteriorPower.map k (1 + t • N)) (exteriorDer k N) ?_ ?_ ?_ v
  · simp only [zero_smul, add_zero, Module.End.one_eq_id, exteriorPower.map_id]
  · intro s t
    have hmul : (1 + s • N) * (1 + t • N) = 1 + (s + t) • N := by
      simp only [mul_add, add_mul, mul_one, one_mul, smul_mul_assoc, mul_smul_comm,
        hN, smul_zero, add_zero, add_smul]
      abel
    rw [← hmul, Module.End.mul_eq_comp, exteriorPower.map_comp]
    rfl
  · exact paperExterior_exists_polynomial_one_add_smul k N

end HodgeLean.Foundations.Program.G32Native
