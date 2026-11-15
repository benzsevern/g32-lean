import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Degree-divisible signed factors can be removed from a specified Kummer
generator through its original field embedding, retaining the exact remaining
coefficient and a nonzero generator. -/
theorem s2e_c1_signed_unmarked_factors
    {K L J : Type*} [Field K] [Field L] [Fintype J]
    (φ : K →+* L) (z : L) (hz : z ≠ 0) (m : ℕ)
    (c : J → K) (hc : ∀ j, c j ≠ 0) (n : J → ℤ)
    (marked : J → Prop) [DecidablePred marked]
    (hd : ∀ j, ¬ marked j → (m : ℤ) ∣ n j)
    (u : K) (hpower : z ^ m = φ (u * ∏ j, c j ^ n j)) :
    ∃ a : K, a ≠ 0 ∧
      u * ∏ j, c j ^ n j =
        a ^ m * (u * ∏ j ∈ Finset.univ.filter marked, c j ^ n j) ∧
      z / φ a ≠ 0 ∧
      (z / φ a) ^ m = φ (u * ∏ j ∈ Finset.univ.filter marked, c j ^ n j) := by
  classical
  let q (j : J) : ℤ := if h : marked j then 0 else Classical.choose (hd j h)
  have hq (j : J) (hj : ¬ marked j) : n j = (m : ℤ) * q j := by
    simpa only [q, dif_neg hj] using Classical.choose_spec (hd j hj)
  let a : K := ∏ j ∈ Finset.univ.filter (fun j => ¬ marked j), c j ^ q j
  have ha : a ≠ 0 := Finset.prod_ne_zero_iff.mpr fun j _ => zpow_ne_zero _ (hc j)
  have hp : (∏ j ∈ Finset.univ.filter (fun j => ¬ marked j), c j ^ n j) = a ^ m := by
    dsimp only [a]
    rw [← Finset.prod_pow]
    apply Finset.prod_congr rfl
    intro j hj
    rw [hq j (Finset.mem_filter.mp hj).2, mul_comm (m : ℤ), zpow_mul, zpow_natCast]
  have hsplit : (∏ j, c j ^ n j) =
      (∏ j ∈ Finset.univ.filter marked, c j ^ n j) *
        ∏ j ∈ Finset.univ.filter (fun j => ¬ marked j), c j ^ n j := by
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ marked _).symm
  have heq : u * ∏ j, c j ^ n j =
      a ^ m * (u * ∏ j ∈ Finset.univ.filter marked, c j ^ n j) := by
    rw [hsplit, hp]
    ring
  have hφa : φ a ≠ 0 := (map_ne_zero φ).mpr ha
  refine ⟨a, ha, heq, div_ne_zero hz hφa, ?_⟩
  rw [div_pow, hpower, heq, map_mul, map_pow]
  exact mul_div_cancel_left₀ _ (pow_ne_zero m hφa)

end HodgeLean.Foundations.Program
