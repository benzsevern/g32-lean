import Mathlib.Data.Int.ModEq

/-! Divisibility of complementary branch weights after reduction to nonnegative residues. -/
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem residue_pair_weights_divisible
    (m : ℕ) (hm : 0 < m) (a b : ℤ) (h : (m : ℤ) ∣ a + b) :
    m ∣ (a % (m : ℤ)).toNat + (b % (m : ℤ)).toNat := by
  have hm0 : (m : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  have ha : ((a % (m : ℤ)).toNat : ℤ) = a % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg a hm0)
  have hb : ((b % (m : ℤ)).toNat : ℤ) = b % (m : ℤ) :=
    Int.toNat_of_nonneg (Int.emod_nonneg b hm0)
  have H : (m : ℤ) ∣ ((a % (m : ℤ)).toNat + (b % (m : ℤ)).toNat : ℕ) := by
    rw [Nat.cast_add, ha, hb]
    apply Int.dvd_iff_emod_eq_zero.mpr
    rw [← Int.add_emod]
    exact Int.emod_eq_zero_of_dvd h
  exact Int.natCast_dvd_natCast.mp H

#print axioms residue_pair_weights_divisible
end HodgeLean.Foundations.QuotientDuality
