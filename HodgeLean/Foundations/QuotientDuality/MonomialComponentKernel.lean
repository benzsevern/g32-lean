import HodgeLean.Foundations.AlgebraicGeometry.TameMonomialHelpers.RootCoverNormality

/-! Minimal components detected by the local domains of a smooth root cover. -/
noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry.TameMonomialCover.Helpers
namespace HodgeLean.Foundations.QuotientDuality

theorem minimal_prime_eq_localization_kernel
    (A : Type*) [CommRing A] (p q : Ideal A) (hp : IsMinimalPrime p)
    [q.IsPrime] [IsDomain (Localization.AtPrime q)] (hpq : p ≤ q) :
    RingHom.ker (algebraMap A (Localization.AtPrime q)) = p := by
  letI : p.IsPrime := hp.isPrime
  let L := FractionRing (A ⧸ p)
  let τ : A →+* L := (algebraMap (A ⧸ p) L).comp (Ideal.Quotient.mk p)
  have hker : RingHom.ker τ = p := by
    dsimp only [τ]
    rw [RingHom.ker_comp_of_injective _ (IsFractionRing.injective (A ⧸ p) L), Ideal.mk_ker]
  obtain ⟨σ, hσ, hcomp⟩ := localized_component_embedding (S := Localization.AtPrime q)
    q τ (hker.symm ▸ hp) (hker.symm ▸ hpq)
  exact (RingHom.ker_comp_of_injective (algebraMap A (Localization.AtPrime q)) hσ).symm.trans
    ((congrArg RingHom.ker hcomp).trans hker)

#print axioms minimal_prime_eq_localization_kernel
end HodgeLean.Foundations.QuotientDuality
