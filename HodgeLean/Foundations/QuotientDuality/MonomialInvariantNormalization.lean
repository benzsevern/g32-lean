import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.NormalCover

/-! Identification of the normalization inside a normal integral covering ring. -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem normalization_range_eq_fixed_elements
    {R K A L G : Type*} [CommRing R] [Field K] [CommRing A] [IsDomain A]
    [IsIntegrallyClosed A] [Field L] [Algebra R K] [Algebra R A]
    [Algebra A L] [Algebra R L] [IsScalarTower R A L] [IsFractionRing A L]
    [Algebra.IsIntegral R A] (f : K →ₐ[R] L)
    (σ : G → (A ≃ₐ[R] A)) (τ : G → (L ≃ₐ[R] L))
    (hcompat : ∀ g a, algebraMap A L (σ g a) = τ g (algebraMap A L a))
    (hfixed : ∀ z : L, (∀ g, τ g z = z) ↔ ∃ k : K, f k = z) :
    ∃ β : integralClosure R K →ₐ[R] A, Function.Injective β ∧
      (∀ b, algebraMap A L (β b) = f (b : K)) ∧
      ∀ a : A, (∃ b, β b = a) ↔ ∀ g, σ g a = a := by
  obtain ⟨β, hβ⟩ := integralClosure_lift_to_normal_cover (R := R) (K := K) (A := A) (L := L) f
  have hinjA := IsFractionRing.injective A L
  have hinjβ : Function.Injective β := by
    intro a b hab
    apply Subtype.ext
    apply f.injective
    exact (hβ a).symm.trans ((congrArg (algebraMap A L) hab).trans (hβ b))
  refine ⟨β, hinjβ, hβ, fun a => ⟨?_, ?_⟩⟩
  · rintro ⟨b, rfl⟩ g
    apply hinjA
    rw [hcompat, hβ]
    exact (hfixed (f (b : K))).2 ⟨b, rfl⟩ g
  · intro ha
    have hτ : ∀ g, τ g (algebraMap A L a) = algebraMap A L a := by
      intro g
      rw [← hcompat, ha g]
    obtain ⟨k, hk⟩ := (hfixed (algebraMap A L a)).1 hτ
    have hint : IsIntegral R k := (isIntegral_algHom_iff f f.injective).1 (by
      rw [hk]
      exact (Algebra.IsIntegral.isIntegral a).map (IsScalarTower.toAlgHom R A L))
    refine ⟨⟨k, hint⟩, hinjA ?_⟩
    exact (hβ ⟨k, hint⟩).trans hk

#print axioms normalization_range_eq_fixed_elements
end HodgeLean.Foundations.QuotientDuality
