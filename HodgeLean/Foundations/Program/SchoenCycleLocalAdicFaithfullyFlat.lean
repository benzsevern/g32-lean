import Mathlib.RingTheory.AdicCompletion.AsTensorProduct
import Mathlib.RingTheory.AdicCompletion.LocalRing
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual maximal-adic scalar extension of a Noetherian local ring is faithfully flat.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_local_adic_faithfullyFlat
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) :=
  Module.FaithfullyFlat.of_flat_of_isLocalHom

#print axioms s2e_local_adic_faithfullyFlat
end HodgeLean.Foundations.Program
