import HodgeLean.Foundations.Program.SchoenCycleAdicMapFiniteJets
import HodgeLean.Foundations.Program.SchoenCycleAdicIdealPowerValues

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The canonical adic extension preserves every power of the actual extended defining ideals.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_algebra_map_preserves_extended_powers
    {k R S : Type*} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
    (I : Ideal R) (J : Ideal S) (hI : I.FG) (hJ : J.FG) (f : R →ₐ[k] S)
    (h : ∀ n r, r ∈ I ^ n → f r ∈ J ^ n)
    (n : ℕ) (r : AdicCompletion I R)
    (hr : r ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ n) :
    s2e_adic_algebra_map I J f h r ∈
      (J.map (algebraMap S (AdicCompletion J S))) ^ n := by
  apply (s2e_adic_extended_power_mem_iff J hJ n _).mpr
  exact s2e_adic_algebra_map_zero_jet I J f h n r
    ((s2e_adic_extended_power_mem_iff I hI n r).mp hr)

#print axioms s2e_adic_algebra_map_preserves_extended_powers
end HodgeLean.Foundations.Program
