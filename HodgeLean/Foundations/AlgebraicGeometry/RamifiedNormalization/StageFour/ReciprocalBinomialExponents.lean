import Mathlib.Data.Nat.GCD.Basic

set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Complementary binomial exponents retain the gcd labels and the complementary reduced exponent. -/
theorem reciprocal_binomial_exponents
    (m α : ℕ) (hm : 0 < m) (hα : α ≤ m) :
    Nat.gcd m (m - α) = Nat.gcd m α ∧
      (m - α) / Nat.gcd m (m - α) = m / Nat.gcd m α - α / Nat.gcd m α := by
  refine ⟨Nat.gcd_self_sub_right hα, ?_⟩
  rw [Nat.gcd_self_sub_right hα]
  let g := Nat.gcd m α
  have hg : 0 < g := Nat.gcd_pos_of_pos_left α hm
  have hmg : g * (m / g) = m := Nat.mul_div_cancel' (Nat.gcd_dvd_left m α)
  have hαg : g * (α / g) = α := Nat.mul_div_cancel' (Nat.gcd_dvd_right m α)
  calc
    (m - α) / g = (g * (m / g - α / g)) / g := by
      rw [Nat.mul_sub_left_distrib, hmg, hαg]
    _ = m / g - α / g := Nat.mul_div_cancel_left _ hg

end AlgebraicGeometry.RamifiedNormalization.StageFour
