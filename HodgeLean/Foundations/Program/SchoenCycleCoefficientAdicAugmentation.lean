import Mathlib.RingTheory.MvPowerSeries.Equiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The coefficient-origin adic algebra has its actual constant-coefficient scalar augmentation.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
def s2e_coefficient_adic_augmentation
    (R σ : Type*) [CommRing R] [Finite σ] :
    AdicCompletion (MvPolynomial.idealOfVars σ R) (MvPolynomial σ R) →ₐ[R] R := by
  let ε : MvPowerSeries σ R →ₐ[R] R :=
    { toRingHom := MvPowerSeries.constantCoeff
      commutes' := fun r => by
        change MvPowerSeries.constantCoeff (MvPowerSeries.C r) = r
        simp }
  exact ε.comp ((MvPowerSeries.toAdicCompletionAlgEquiv σ R).restrictScalars R).symm.toAlgHom

#print axioms s2e_coefficient_adic_augmentation
end HodgeLean.Foundations.Program
