import Mathlib.Analysis.Complex.Basic

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Scaling the base coordinate removes the initial selector root and retains the literal phase power for every label. -/
theorem binomial_phase_normalization
    (κ ζ : ℂ) (hκ : κ ≠ 0) (B : ℤ) (n l : ℕ) :
    κ ^ B * (κ * (ζ ^ n) ^ l) ^ (-B) =
      (ζ ^ B) ^ (-((n * l : ℕ) : ℤ)) := by
  rw [mul_zpow, ← mul_assoc, ← zpow_add₀ hκ, add_neg_cancel, zpow_zero, one_mul]
  rw [← pow_mul, ← zpow_natCast, ← zpow_mul, ← zpow_mul]
  congr 1
  ring

end AlgebraicGeometry.RamifiedNormalization.StageFour
