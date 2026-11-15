import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorOrderCorrection

noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Integer prime orders of weighted products are the weighted sums of the orders. -/
theorem s2v_l1b_divisor_weighted_product_order
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    {J : Type*} (g : J → R) (n : J → ℕ) (hg : ∀ j, g j ≠ 0)
    (p : R) (hp : Prime p) (s : Finset J) :
    ((emultiplicity p (∏ j ∈ s, g j ^ n j)).toNat : ℤ) =
      ∑ j ∈ s, (n j : ℤ) * ((emultiplicity p (g j)).toNat : ℤ) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp only [Finset.prod_empty, Finset.sum_empty,
      emultiplicity_of_one_right hp.not_isUnit, ENat.toNat_zero, Int.natCast_zero]
  | @insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj,
      s2v_l1b_kval_prime_order_mul hp (pow_ne_zero _ (hg j))
        (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hg k)),
      s2v_l1b_kval_prime_order_pow hp, ih]

end HodgeLean.Foundations.Program
