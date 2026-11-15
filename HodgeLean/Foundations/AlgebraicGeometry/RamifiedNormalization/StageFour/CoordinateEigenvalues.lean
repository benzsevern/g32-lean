import Mathlib.Algebra.Field.Equiv
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Tactic.Ring

set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The original generator's scalar determines both the selector and the Bezout parameter action. -/
theorem binomial_coordinate_eigenvalues
    {K : Type*} [Field K] (φ : K ≃+* K) (s w c : K)
    (hs : φ s = s) (hw : φ w = c * w)
    (n a : ℕ) (A B : ℤ) :
    φ (w ^ n / s ^ a) = c ^ n * (w ^ n / s ^ a) ∧
      φ (s ^ A * w ^ B) = c ^ B * (s ^ A * w ^ B) := by
  constructor
  · rw [map_div₀, map_pow, map_pow, hs, hw, mul_pow]
    ring
  · rw [map_mul, map_zpow₀, map_zpow₀, hs, hw, mul_zpow]
    ring

end AlgebraicGeometry.RamifiedNormalization.StageFour
