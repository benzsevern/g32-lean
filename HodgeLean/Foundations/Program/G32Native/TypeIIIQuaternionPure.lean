import HodgeLean.Foundations.Program.G32Native.TypeIIIQuaternionDivision

noncomputable section
open scoped Quaternion
namespace HodgeLean.Foundations.Program.G32Native

/-- The reduced norm in a definite presentation is nonnegative. -/
theorem typeIIIQuaternionNorm_nonneg (b : ℚ) (hb : b < 0)
    (q : ℍ[ℚ, -3, 0, b]) : 0 ≤ typeIIIQuaternionNorm b q := by
  have hj := mul_nonneg (show 0 ≤ -b by linarith) (sq_nonneg q.imJ)
  have hk := mul_nonneg (show 0 ≤ -(3 * b) by linarith) (sq_nonneg q.imK)
  dsimp [typeIIIQuaternionNorm]
  nlinarith [sq_nonneg q.re, sq_nonneg q.imI]

/-- The reduced norm of a nonzero definite quaternion is positive. -/
theorem typeIIIQuaternionNorm_pos (b : ℚ) (hb : b < 0)
    (q : ℍ[ℚ, -3, 0, b]) (hq : q ≠ 0) : 0 < typeIIIQuaternionNorm b q := by
  exact lt_of_le_of_ne (typeIIIQuaternionNorm_nonneg b hb q)
    (Ne.symm fun h => hq ((typeIIIQuaternionNorm_eq_zero b hb q).1 h))

/-- A pure quaternion squares to minus its reduced norm. -/
theorem typeIIIQuaternion_pure_square (b : ℚ) (q : ℍ[ℚ, -3, 0, b]) (hq : q.re = 0) :
    q * q = algebraMap ℚ _ (-typeIIIQuaternionNorm b q) := by
  have hs : star q = -q := by ext <;> simp [hq]
  have h := typeIIIQuaternion_mul_star b q
  rw [hs, mul_neg, neg_eq_iff_eq_neg, ← map_neg] at h
  exact h

/-- A quaternion whose square is a negative rational scalar is pure. -/
theorem typeIIIQuaternion_pure_of_square_neg (b c : ℚ) (hc : c < 0)
    (q : ℍ[ℚ, -3, 0, b]) (hsq : q * q = algebraMap ℚ _ c) : q.re = 0 := by
  by_contra hr
  have hi := congrArg QuaternionAlgebra.imI hsq
  have hj := congrArg QuaternionAlgebra.imJ hsq
  have hk := congrArg QuaternionAlgebra.imK hsq
  have hre := congrArg QuaternionAlgebra.re hsq
  simp [QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul, QuaternionAlgebra.re_mul,
    QuaternionAlgebra.algebraMap_eq] at hi hj hk hre
  have hi0 : q.imI = 0 := by
    have : (2 * q.re) * q.imI = 0 := by nlinarith [hi]
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hr)
  have hj0 : q.imJ = 0 := by
    have : (2 * q.re) * q.imJ = 0 := by nlinarith [hj]
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hr)
  have hk0 : q.imK = 0 := by
    have : (2 * q.re) * q.imK = 0 := by nlinarith [hk]
    exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero (by norm_num) hr)
  rw [hi0, hj0, hk0] at hre
  nlinarith [sq_nonneg q.re]

end HodgeLean.Foundations.Program.G32Native

#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionNorm_nonneg
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternionNorm_pos
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_pure_square
#print axioms HodgeLean.Foundations.Program.G32Native.typeIIIQuaternion_pure_of_square_neg
