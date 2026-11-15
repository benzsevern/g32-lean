import Mathlib.RingTheory.Finiteness.Ideal

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A finite-support covering of the prime fibre bounds the support-ideal filtration by the fibre ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapters 1 and 10. -/
theorem s2e_support_intersection_power_le
    {A ι : Type*} [CommRing A] (J : Ideal A) (I : ι → Ideal A)
    (hfg : (⨅ i, I i).FG)
    (hcover : ∀ P : Ideal A, P.IsPrime → J ≤ P → ∃ i, I i ≤ P) :
    ∃ n : ℕ, (⨅ i, I i) ^ n ≤ J := by
  apply Ideal.exists_pow_le_of_le_radical_of_fg _ hfg
  rw [Ideal.radical_eq_sInf]
  apply le_sInf
  intro P hP
  obtain ⟨i, hi⟩ := hcover P hP.2 hP.1
  exact (iInf_le I i).trans hi

#print axioms s2e_support_intersection_power_le
end HodgeLean.Foundations.Program
