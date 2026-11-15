import HodgeLean.Foundations.Program.SchoenCycleC1PairedIntegralHelpers

/-! # Integral inverse derivatives of unit Kummer equations -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open Polynomial
namespace HodgeLean.Foundations.Program

/-- A root of a unit Kummer equation has integral inverse over the base. -/
theorem s2e_c1_kummer_inverse_integral
    {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (m : ℕ) (hm : 0 < m) (c : Rˣ) (z : L)
    (hz : z ^ m = algebraMap R L (c : R)) : IsIntegral R z⁻¹ := by
  apply IsIntegral.of_pow hm
  rw [inv_pow, hz, ← map_units_inv]
  exact isIntegral_algebraMap

/-- The inverse derivative of a unit Kummer equation is integral when the
covering degree is a base-ring unit. -/
theorem s2e_c1_kummer_inverse_derivative_integral
    {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (m : ℕ) (hm : 0 < m) (c d : Rˣ) (hd : (d : R) = (m : R))
    (z : L) (hz : z ^ m = algebraMap R L (c : R)) :
    IsIntegral R (aeval z (derivative (X ^ m - C (c : R) : R[X])))⁻¹ := by
  rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero]
  simp only [map_mul, aeval_C, map_pow, aeval_X]
  rw [mul_inv_rev, ← inv_pow, ← hd, ← map_units_inv]
  exact ((s2e_c1_kummer_inverse_integral m hm c z hz).pow (m - 1)).mul
    isIntegral_algebraMap

end HodgeLean.Foundations.Program
