import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- A common signed weighted residue separates the exact degree power
from the rational product, retaining all signed coefficient orders. -/
theorem s2e_c1_signed_weighted_power_factor
    {K J : Type*} [Field K] [Fintype J]
    (g : J → K) (hg : ∀ j, g j ≠ 0) (k : J → ℕ) (n : J → ℤ)
    (s : ℤ) (m : ℕ) (hn : ∀ j, (m : ℤ) ∣ n j - s * (k j : ℤ)) :
    ∃ a : K, a ≠ 0 ∧ (∏ j, g j ^ n j) = a ^ m * (∏ j, g j ^ k j) ^ s := by
  classical
  let q (j : J) : ℤ := Classical.choose (hn j)
  have hq (j : J) : n j = (k j : ℤ) * s + q j * (m : ℤ) := by
    have h := Classical.choose_spec (hn j)
    change n j - s * (k j : ℤ) = (m : ℤ) * q j at h
    calc
      n j = (m : ℤ) * q j + s * (k j : ℤ) := sub_eq_iff_eq_add.mp h
      _ = _ := by ring
  let a := ∏ j, g j ^ q j
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hg j)
  have he (j : J) : g j ^ n j = (g j ^ k j) ^ s * (g j ^ q j) ^ m := by
    rw [hq, zpow_add₀ (hg j), zpow_mul, zpow_natCast, zpow_mul, zpow_natCast]
  refine ⟨a, ha, ?_⟩
  simp_rw [he]
  rw [Finset.prod_mul_distrib, ← Finset.prod_zpow, ← Finset.prod_pow]
  exact mul_comm _ _

end HodgeLean.Foundations.Program
