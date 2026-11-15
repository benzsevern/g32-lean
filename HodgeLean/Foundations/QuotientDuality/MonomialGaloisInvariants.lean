import HodgeLean.Foundations.QuotientDuality.MonomialIntegralGaloisAction
import HodgeLean.Foundations.QuotientDuality.MonomialInvariantNormalization
import Mathlib.FieldTheory.Galois.Basic

/-! The normalization is the fixed subring of a finite Galois normal covering algebra. -/
noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem galois_cover_normalization_invariants
    {R K A F : Type*} [CommRing R] [Field K] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field F]
    [Algebra R K] [Algebra K F] [Algebra R F] [IsScalarTower R K F]
    [Algebra R A] [Algebra A F] [IsScalarTower R A F] [IsFractionRing A F]
    [Algebra.IsIntegral R A] [IsGalois K F] [FiniteDimensional K F] :
    ∃ (ρ : (F ≃ₐ[K] F) →* (A ≃ₐ[R] A)) (β : integralClosure R K →ₐ[R] A),
      Function.Injective β ∧
      (∀ g a, algebraMap A F (ρ g a) = g (algebraMap A F a)) ∧
      (∀ b, algebraMap A F (β b) = algebraMap K F (b : K)) ∧
      ∀ a : A, (∃ b, β b = a) ↔ ∀ g, ρ g a = a := by
  obtain ⟨ρ, hρ⟩ := integral_cover_galois_action (R := R) (K := K) (A := A) (F := F)
  obtain ⟨β, hβ, hβF, hfixed⟩ := normalization_range_eq_fixed_elements
    (IsScalarTower.toAlgHom R K F) ρ (fun g => g.restrictScalars R) hρ (by
      intro z
      exact (IsGalois.mem_range_algebraMap_iff_fixed (F := K) (E := F) z).symm)
  exact ⟨ρ, β, hβ, hρ, hβF, hfixed⟩

#print axioms galois_cover_normalization_invariants
end HodgeLean.Foundations.QuotientDuality
