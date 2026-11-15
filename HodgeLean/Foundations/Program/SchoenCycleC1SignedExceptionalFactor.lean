import Mathlib.Algebra.Field.Basic
import Mathlib.Tactic.Ring

/-! # Signed exceptional factors in paired rational equations -/
noncomputable section
namespace HodgeLean.Foundations.Program

/-- Degree-divisible signed exceptional exponents factor as an exact degree
power, including negative orders of the exceptional parameter. -/
theorem s2e_c1_signed_exceptional_factor
    {K : Type*} [Field K] (x v u : K) (hx : x ≠ 0)
    (a b q : ℤ) (m : ℕ) (hab : a + b = (m : ℤ) * q) :
    x ^ a * (x * v) ^ b * u = (x ^ q) ^ m * (v ^ b * u) := by
  rw [mul_zpow]
  calc
    x ^ a * (x ^ b * v ^ b) * u = x ^ (a + b) * (v ^ b * u) := by
      rw [zpow_add₀ hx]
      ring
    _ = (x ^ q) ^ m * (v ^ b * u) := by
      rw [hab, mul_comm (m : ℤ) q, zpow_mul, zpow_natCast]

end HodgeLean.Foundations.Program
