import Mathlib.RingTheory.AdicCompletion.LocalRing

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Powers of the actual extended adic ideal are detected by the actual finite quotient coordinate.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_adic_extended_power_mem_iff
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (N : ℕ) (x : AdicCompletion I R) :
    x ∈ (I.map (algebraMap R (AdicCompletion I R))) ^ N ↔ x.val N = 0 := by
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hI]
  rfl

#print axioms s2e_adic_extended_power_mem_iff
end HodgeLean.Foundations.Program
