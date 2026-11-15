import HodgeLean.Foundations.Program.SchoenTowerL1bTransportCharacterRoot

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- The primitive signed scalar on a stabilizer is the corresponding power of the global scalar. -/
theorem s2v_l1b_divisor_signed_scalar_power
    {m d q : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) (hme : m = d * q) (s : ℤ) :
    Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (m : ℂ)) ^ q =
      Complex.exp ((s : ℂ) * (2 * Real.pi * Complex.I) / (d : ℂ)) := by
  have hq : q ≠ 0 := by intro h; rw [h, mul_zero] at hme; exact hm hme
  rw [← Complex.exp_nat_mul]
  congr 1
  rw [hme, Nat.cast_mul]
  have hdC : (d : ℂ) ≠ 0 := by exact_mod_cast hd
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq
  field_simp

end HodgeLean.Foundations.Program
