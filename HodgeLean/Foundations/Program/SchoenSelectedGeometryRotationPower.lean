import HodgeLean.Foundations.Program.SchoenSelectedGeometryChartMultiplier

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- A positive root raised by a stabilizer index is the positive root of the quotient order. -/
theorem s0_positive_rotation_power (a b : ℕ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Complex.exp (2 * Real.pi * Complex.I / (a * b : ℕ)) ^ b =
      Complex.exp (2 * Real.pi * Complex.I / a) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  have ha' : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha
  have hb' : (b : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hb
  field_simp

#print axioms s0_positive_rotation_power
end HodgeLean.Foundations.Program
