import HodgeLean.Adapters.NormalConeB4aGysinSmallDeformation
import Mathlib.Data.ENat.BigOperators

noncomputable section
namespace HodgeLean.Adapters

/-- A finite length sum transports through an equivalence with rational weights. -/
theorem a3b4a_gysin_sum_weights_of_length_equiv
    {I J : Type*} [Fintype I] [Fintype J] (E : I ≃ J)
    (length : I → ℕ∞) (weight : J → ℚ) (m : ℕ)
    (hsum : ∑ x, length x = m)
    (hweight : ∀ x, ∃ k : ℕ, length x = k ∧ weight (E x) = k) :
    ∑ y, weight y = m := by
  classical
  choose k hk hw using hweight
  have hn : ∑ x, k x = m := by
    apply ENat.coe_inj.mp
    simpa only [Nat.cast_sum, ← hk] using hsum
  calc
    ∑ y, weight y = ∑ x, weight (E x) := (Equiv.sum_comp E weight).symm
    _ = ∑ x, (k x : ℚ) := Finset.sum_congr rfl fun x _ => hw x
    _ = m := by rw [← Nat.cast_sum, hn]

end HodgeLean.Adapters
