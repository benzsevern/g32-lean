import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.RingTheory.Ideal.Operations

/-! # A leading-term approximation detects a local unit factor -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A factor preserving a nonzero ideal-quotient class is a unit in a local ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 2. -/
theorem s2e_isUnit_of_product_approximation
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R)
    (p q : R) (hp : p ∉ I) (he : p * q - p ∈ I) : IsUnit q := by
  by_contra hq
  have hqm : q ∈ IsLocalRing.maximalIdeal R := hq
  have hu : IsUnit (q - 1) := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    have h1 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
      simpa only [sub_sub_cancel] using (IsLocalRing.maximalIdeal R).sub_mem hqm hm
    exact (show ¬IsUnit (1 : R) from h1) isUnit_one
  apply hp
  apply (Ideal.unit_mul_mem_iff_mem I hu).mp
  simpa only [sub_mul, one_mul, mul_comm q p] using he

end HodgeLean.Foundations.Program
