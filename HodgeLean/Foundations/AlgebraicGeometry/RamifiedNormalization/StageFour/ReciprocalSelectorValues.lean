import Mathlib.Algebra.Field.Basic

set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Dividing the generator by the ratio leaves the selector unchanged in the reciprocal chart. -/
theorem reciprocal_binomial_selector_value
    {L : Type} [Field L] (n a : ℕ) (ha : a ≤ n) (w s : L) (hs : s ≠ 0) :
    (w / s) ^ n / (s⁻¹) ^ (n - a) = w ^ n / s ^ a := by
  rw [div_pow, inv_pow, div_inv_eq_mul]
  have hpow : s ^ (n - a) * s ^ a = s ^ n := by
    rw [← pow_add, Nat.sub_add_cancel ha]
  apply (eq_div_iff (pow_ne_zero a hs)).mpr
  calc
    (w ^ n / s ^ n * s ^ (n - a)) * s ^ a =
        (w ^ n / s ^ n) * (s ^ (n - a) * s ^ a) := mul_assoc _ _ _
    _ = (w ^ n / s ^ n) * s ^ n := by rw [hpow]
    _ = w ^ n := div_mul_cancel₀ _ (pow_ne_zero n hs)

end AlgebraicGeometry.RamifiedNormalization.StageFour
