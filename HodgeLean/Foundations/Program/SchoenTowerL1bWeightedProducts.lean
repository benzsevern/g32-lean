import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Weighted products retain every exceptional factor, with its total multiplicity. -/
theorem s2v_l1b_weighted_product_transport
    {R J K : Type*} [CommMonoid R] [Fintype J] [Fintype K]
    (g d : J → R) (E : K → R) (n : J → ℕ) (a : K → J → ℕ)
    (hg : ∀ j, g j = d j * ∏ k, E k ^ a k j) :
    (∏ j, g j ^ n j) = (∏ j, d j ^ n j) *
      ∏ k, E k ^ (∑ j, a k j * n j) := by
  simp_rw [hg, mul_pow, ← Finset.prod_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_comm]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  rw [Finset.prod_pow_eq_pow_sum]

/-- Each pair of branch weights contributes one full covering degree. -/
theorem s2v_l1b_pair_weight_sum
    {J K : Type*} [Fintype J] [DecidableEq J]
    (p q : K → J) (hpq : ∀ k, p k ≠ q k) (n : J → ℕ)
    (m : ℕ) (hn : ∀ k, n (p k) + n (q k) = m) (k : K) :
    (∑ j, (if j = p k then 1 else if j = q k then 1 else 0) * n j) = m := by
  classical
  have heq (j : J) :
      (if j = p k then 1 else if j = q k then 1 else 0) * n j =
        (if j = p k then n (p k) else 0) +
          (if j = q k then n (q k) else 0) := by
    by_cases hp : j = p k
    · subst j
      simp only [ite_true, hpq k, ite_false, one_mul, add_zero]
    · by_cases hq : j = q k
      · subst j
        simp only [hp, ite_false, ite_true, one_mul, zero_add]
      · simp only [hp, hq, ite_false, zero_mul, add_zero]
  simp_rw [heq]
  rw [Finset.sum_add_distrib]
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, ite_true] using hn k

/-- Paired branch factors give the full exceptional product to the covering degree. -/
theorem s2v_l1b_paired_product_transport
    {R J K : Type*} [CommMonoid R] [Fintype J] [Fintype K] [DecidableEq J]
    (g d : J → R) (E : K → R) (n : J → ℕ)
    (p q : K → J) (hpq : ∀ k, p k ≠ q k)
    (m : ℕ) (hn : ∀ k, n (p k) + n (q k) = m)
    (hg : ∀ j, g j = d j *
      ∏ k, E k ^ (if j = p k then 1 else if j = q k then 1 else 0)) :
    (∏ j, g j ^ n j) = (∏ j, d j ^ n j) * (∏ k, E k) ^ m := by
  rw [s2v_l1b_weighted_product_transport g d E n _ hg]
  simp_rw [s2v_l1b_pair_weight_sum p q hpq n m hn]
  rw [Finset.prod_pow]

/-- The remaining weighted product has precisely the two selected factors off all other supports. -/
theorem s2v_l1b_weighted_product_two_factors
    {R J : Type*} [CommMonoid R] [Fintype J] [DecidableEq J]
    (d : J → R) (n : J → ℕ) (p q : J) (hpq : p ≠ q)
    (hd : ∀ j, j ≠ p → j ≠ q → d j = 1) :
    (∏ j, d j ^ n j) = d p ^ n p * d q ^ n q := by
  have heq : (∏ j, d j ^ n j) = ∏ j ∈ ({p, q} : Finset J), d j ^ n j := by
    symm
    apply Finset.prod_subset (Finset.subset_univ _)
    intro j _ hj
    have hjp : j ≠ p := fun h => hj (by simp only [h, Finset.mem_insert, true_or])
    have hjq : j ≠ q := fun h => hj (by simp only [h, Finset.mem_insert,
      Finset.mem_singleton, or_true])
    rw [hd j hjp hjq, one_pow]
  rw [heq, Finset.prod_pair hpq]

end HodgeLean.Foundations.Program
