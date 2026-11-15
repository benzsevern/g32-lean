import HodgeLean.Foundations.Program.SchoenCycleLocalAdicFaithfullyFlat
import HodgeLean.Foundations.Program.SchoenCycleAdicMapValues

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Equality of actual local functions can be reflected from their canonical maximal-adic images.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_actual_invariant_of_formal_invariant
    {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
    [IsLocalRing R] [IsNoetherianRing R]
    (f : R →ₐ[k] R)
    (hf : ∀ n r, r ∈ IsLocalRing.maximalIdeal R ^ n →
      f r ∈ IsLocalRing.maximalIdeal R ^ n)
    (r : R)
    (hr : s2e_adic_algebra_map _ _ f hf
      (AdicCompletion.of (IsLocalRing.maximalIdeal R) R r) =
        AdicCompletion.of (IsLocalRing.maximalIdeal R) R r) : f r = r := by
  letI := s2e_local_adic_faithfullyFlat R
  apply FaithfulSMul.algebraMap_injective R
    (AdicCompletion (IsLocalRing.maximalIdeal R) R)
  rw [s2e_adic_algebra_map_of] at hr
  exact hr

#print axioms s2e_actual_invariant_of_formal_invariant
end HodgeLean.Foundations.Program
