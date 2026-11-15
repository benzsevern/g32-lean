import HodgeLean.Foundations.AbelianQuotient.PeriodExtension

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.RealDefs HodgeLean.Foundations HodgeLean.Adapters
open scoped CategoryTheory.MonObj
namespace HodgeLean.Foundations.AbelianQuotient

/-- An integral multiple of a right inverse suffices for rational character descent. -/
theorem character_descent_of_multiple {L M : Type*} [AddCommGroup L] [AddCommGroup M]
    (φ : L →+ M) (ψ : M →+ L) (N : ℕ) (hN : 0 < N)
    (hψ : ∀ m, φ (ψ m) = N • m) (χ : L →+ ℚ)
    (hχ : ∀ l, φ l = 0 → χ l = 0) :
    ∃ chiQ : M →+ ℚ, ∀ l, chiQ (φ l) = χ l := by
  refine ⟨(N : ℚ)⁻¹ • (χ.comp ψ), ?_⟩
  intro l
  have hd : φ (ψ (φ l) - N • l) = 0 := by
    rw [map_sub, map_nsmul, hψ, sub_self]
  have he := hχ (ψ (φ l) - N • l) hd
  rw [map_sub, map_nsmul, sub_eq_zero, nsmul_eq_mul] at he
  change (N : ℚ)⁻¹ * χ (ψ (φ l)) = χ l
  rw [he, ← mul_assoc, inv_mul_cancel₀ (show (N : ℚ) ≠ 0 by exact_mod_cast hN.ne'), one_mul]

end HodgeLean.Foundations.AbelianQuotient
