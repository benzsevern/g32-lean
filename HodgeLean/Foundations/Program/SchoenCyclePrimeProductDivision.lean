import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # Simultaneous division by distinct prime factors -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 400000
open scoped BigOperators Classical
namespace HodgeLean.Foundations.Program

/-- Distinct prime factors dividing an element divide it simultaneously, without a factorization structure on the ring.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.4, printed p. 15;
Atiyah–Macdonald, Introduction to Commutative Algebra, Chapter 1. -/
theorem s2e_distinct_prime_product_dvd
    {R α : Type*} [CommMonoidWithZero R] (f : α → R) (S : Finset α) :
    (∀ i ∈ S, Prime (f i)) →
    (∀ i ∈ S, ∀ j ∈ S, i ≠ j → ¬f i ∣ f j) →
    ∀ z : R, (∀ i ∈ S, f i ∣ z) → (∏ i ∈ S, f i) ∣ z := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro _ _ z _
    simpa only [Finset.prod_empty] using one_dvd z
  | @insert i S hi ih =>
    intro hp hpair z hz
    obtain ⟨r, hr⟩ := hz i (Finset.mem_insert_self i S)
    have hdiv (j : α) (hj : j ∈ S) : f j ∣ r := by
      have hd := hz j (Finset.mem_insert_of_mem hj)
      rw [hr] at hd
      apply ((hp j (Finset.mem_insert_of_mem hj)).dvd_mul.mp hd).resolve_left
      apply hpair j (Finset.mem_insert_of_mem hj) i (Finset.mem_insert_self i S)
      intro hji
      exact hi (hji ▸ hj)
    obtain ⟨t, ht⟩ := ih
      (fun j hj => hp j (Finset.mem_insert_of_mem hj))
      (fun j hj k hk => hpair j (Finset.mem_insert_of_mem hj) k (Finset.mem_insert_of_mem hk))
      r hdiv
    refine ⟨t, ?_⟩
    rw [Finset.prod_insert hi, hr, ht, mul_assoc]

end HodgeLean.Foundations.Program
