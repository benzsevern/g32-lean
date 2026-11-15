import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Operations

/-! # Base-linear actions preserve extended adic ideals -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Every base-linear endomorphism preserves all powers of an ideal extended from the base.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 10. -/
theorem s2e_linear_preserves_extended_ideal_powers
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (I : Ideal R) (f : B →ₗ[R] B) :
    ∀ n : ℕ, ∀ b ∈ (I.map (algebraMap R B)) ^ n,
      f b ∈ (I.map (algebraMap R B)) ^ n := by
  have hJ (n : ℕ) : ((I.map (algebraMap R B)) ^ n).restrictScalars R =
      (I ^ n • ⊤ : Submodule R B) := by
    rw [← Ideal.map_pow, ← Ideal.smul_top_eq_map]
  intro n b hb
  have hb' : b ∈ (I ^ n • ⊤ : Submodule R B) := by
    rw [← hJ n]
    exact hb
  change f b ∈ ((I.map (algebraMap R B)) ^ n).restrictScalars R
  rw [hJ n]
  refine Submodule.smul_induction_on hb' ?_ ?_
  · intro c hc y hy
    rw [map_smul]
    exact Submodule.smul_mem_smul hc hy
  · intro y z hy hz
    rw [map_add]
    exact Submodule.add_mem _ hy hz

#print axioms s2e_linear_preserves_extended_ideal_powers
end HodgeLean.Foundations.Program
