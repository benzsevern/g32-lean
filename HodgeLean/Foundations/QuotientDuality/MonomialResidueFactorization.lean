import Mathlib.Algebra.Field.Basic
import Mathlib.Data.Int.ModEq

/-! Factoring an integer branch exponent into a residue and a full covering power. -/
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem zpow_eq_residue_mul_power
    {K : Type*} [Field K] (m : ℕ) (hm : 0 < m) (g : K) (hg : g ≠ 0) (a : ℤ) :
    g ^ a = (g ^ (a / (m : ℤ))) ^ m * g ^ (a % (m : ℤ)).toNat := by
  have hm0 : (m : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have hres : ((a % (m : ℤ)).toNat : ℤ) = a % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg a hm0)
  have ha : a = ((a % (m : ℤ)).toNat : ℤ) + (a / (m : ℤ)) * (m : ℤ) := by
    rw [hres]
    simpa only [Int.mul_comm] using (Int.emod_add_mul_ediv a (m : ℤ)).symm
  calc
    g ^ a = g ^ (((a % (m : ℤ)).toNat : ℤ) + (a / (m : ℤ)) * (m : ℤ)) :=
      congrArg (fun z : ℤ => g ^ z) ha
    _ = (g ^ (a / (m : ℤ))) ^ m * g ^ (a % (m : ℤ)).toNat := by
      rw [zpow_add₀ hg, zpow_mul, zpow_natCast, zpow_natCast, mul_comm]

#print axioms zpow_eq_residue_mul_power
end HodgeLean.Foundations.QuotientDuality
