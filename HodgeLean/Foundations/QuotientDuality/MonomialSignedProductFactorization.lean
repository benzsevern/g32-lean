import HodgeLean.Foundations.QuotientDuality.MonomialResidueFactorization
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset

/-! Nonnegative residues and exact covering powers in a signed branch product. -/
noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

theorem signed_branch_product_residue_factorization
    {K J : Type*} [Field K] [Fintype J]
    (m : ℕ) (hm : 0 < m) (g : J → K) (hg : ∀ j, g j ≠ 0) (a : J → ℤ) :
    (∏ j, g j ^ a j) = (∏ j, g j ^ (a j / (m : ℤ))) ^ m *
      ∏ j, g j ^ (a j % (m : ℤ)).toNat := by
  calc
    (∏ j, g j ^ a j) =
        ∏ j, ((g j ^ (a j / (m : ℤ))) ^ m * g j ^ (a j % (m : ℤ)).toNat) := by
      apply Finset.prod_congr rfl
      intro j _
      exact zpow_eq_residue_mul_power m hm (g j) (hg j) (a j)
    _ = _ := by rw [Finset.prod_mul_distrib, ← Finset.prod_pow]

#print axioms signed_branch_product_residue_factorization
end HodgeLean.Foundations.QuotientDuality
