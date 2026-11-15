import Mathlib.RingTheory.MvPowerSeries.Equiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The finite-variable coefficient-origin adic polynomial algebra over a Noetherian scalar ring is Noetherian.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_coefficient_adic_isNoetherianRing
    (R σ : Type*) [CommRing R] [IsNoetherianRing R] [Finite σ] :
    IsNoetherianRing (AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R)) :=
  isNoetherianRing_of_ringEquiv (MvPowerSeries σ R)
    (MvPowerSeries.toAdicCompletionAlgEquiv σ R).toRingEquiv

#print axioms s2e_coefficient_adic_isNoetherianRing
end HodgeLean.Foundations.Program
