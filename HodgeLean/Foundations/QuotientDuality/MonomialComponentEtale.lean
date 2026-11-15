import HodgeLean.Foundations.QuotientDuality.MonomialComponentIdempotent

/-! Integral components of a locally normal root cover remain etale over that cover. -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.QuotientDuality

theorem minimal_component_quotient_etale
    (A : Type*) [CommRing A] [IsNoetherianRing A]
    (hlocal : ∀ (q : Ideal A) [q.IsPrime], IsDomain (Localization.AtPrime q))
    (p : Ideal A) (hp : IsMinimalPrime p) : (Ideal.Quotient.mk p).Etale := by
  letI : Algebra.FinitePresentation A (A ⧸ p) :=
    Algebra.FinitePresentation.quotient (IsNoetherian.noetherian p)
  letI : Algebra.FormallyEtale A (A ⧸ p) :=
    (Algebra.FormallyEtale.iff_of_surjective
      (show Function.Surjective (algebraMap A (A ⧸ p)) from Ideal.Quotient.mk_surjective)).2 (by
        change IsIdempotentElem (RingHom.ker (Ideal.Quotient.mk p))
        rw [Ideal.mk_ker]
        exact minimal_prime_idempotent_of_local_domains A hlocal p hp)
  exact (RingHom.etale_algebraMap).2 (show Algebra.Etale A (A ⧸ p) from {})

#print axioms minimal_component_quotient_etale
end HodgeLean.Foundations.QuotientDuality
