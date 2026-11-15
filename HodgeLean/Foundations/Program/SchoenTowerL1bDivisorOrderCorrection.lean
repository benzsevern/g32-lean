import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorPowerFactors
import HodgeLean.Foundations.Program.SchoenTowerL1bKvalResidueTransport

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Congruent signed prime orders give a unit and nonzero rational power correction. -/
theorem s2v_l1b_divisor_correction_of_orders
    {R : Type*} [CommRing R] [IsDomain R] [UniqueFactorizationMonoid R]
    (a b P : R) (ha : a ≠ 0) (hb : b ≠ 0) (hP : P ≠ 0)
    (m : ℕ) (hm : 0 < m)
    (hv : ∀ p : R, Prime p → Int.ModEq (m : ℤ)
      (((emultiplicity p a).toNat : ℤ) - ((emultiplicity p b).toNat : ℤ))
      ((emultiplicity p P).toNat : ℤ)) :
    ∃ (ε : Rˣ) (A B : R), A ≠ 0 ∧ B ≠ 0 ∧
      a * B ^ m = (ε : R) * b * P * A ^ m := by
  have hbP : b * P ≠ 0 := mul_ne_zero hb hP
  let H := a * (b * P) ^ (m - 1)
  have hH : H ≠ 0 := mul_ne_zero ha (pow_ne_zero _ hbP)
  have hd (p : R) (hp : Prime p) : m ∣ (emultiplicity p H).toNat := by
    apply Int.natCast_dvd_natCast.mp
    have hh := Int.dvd_sub (dvd_mul_right (m : ℤ)
      (((emultiplicity p b).toNat : ℤ) + ((emultiplicity p P).toNat : ℤ)))
      (Int.modEq_iff_dvd.mp (hv p hp))
    change (m : ℤ) ∣ ((emultiplicity p (a * (b * P) ^ (m - 1))).toNat : ℤ)
    rw [s2v_l1b_kval_prime_order_mul hp ha (pow_ne_zero _ hbP),
      s2v_l1b_kval_prime_order_pow hp,
      s2v_l1b_kval_prime_order_mul hp hb hP,
      Nat.cast_sub (show 1 ≤ m by omega), Nat.cast_one]
    convert hh using 1 <;> ring
  obtain ⟨ε, c, hc, heq⟩ := s2v_l1b_divisor_power_of_orders H hH m hd
  refine ⟨ε, c, b * P, hc, hbP, ?_⟩
  calc
    a * (b * P) ^ m = H * (b * P) := by
      dsimp only [H]
      have hpowe : (b * P) ^ m = (b * P) ^ (m - 1) * (b * P) := by
        rw [← pow_succ, Nat.sub_add_cancel (show 1 ≤ m by omega)]
      rw [hpowe]
      ring
    _ = (ε : R) * b * P * c ^ m := by rw [heq]; ring

end HodgeLean.Foundations.Program
