import Mathlib.RingTheory.AdicCompletion.LocalRing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Adic passage at any finitely generated maximal ideal gives a local ring, without assuming the original ring local.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_maximal_adic_isLocalRing
    {R : Type*} [CommRing R] (I : Ideal R) [I.IsMaximal] (hI : I.FG) :
    IsLocalRing (AdicCompletion I R) := by
  haveI := AdicCompletion.isMaximal_map_of_le I I le_rfl hI
  haveI := AdicCompletion.isAdicComplete_self I hI
  exact isLocalRing_of_isAdicComplete_maximal (I.map (algebraMap R (AdicCompletion I R)))

#print axioms s2e_maximal_adic_isLocalRing
end HodgeLean.Foundations.Program
