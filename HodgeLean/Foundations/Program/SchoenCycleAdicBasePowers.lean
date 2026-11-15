import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-! # Adic filtration of the actual base algebra map -/
noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The actual base algebra map preserves every power into the extended ideal.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_base_map_preserves_extended_ideal_powers
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B] (I : Ideal R) :
    ∀ n : ℕ, ∀ r ∈ I ^ n, algebraMap R B r ∈ (I.map (algebraMap R B)) ^ n := by
  intro n r hr
  rw [← Ideal.map_pow]
  exact Ideal.mem_map_of_mem (algebraMap R B) hr

#print axioms s2e_base_map_preserves_extended_ideal_powers
end HodgeLean.Foundations.Program
