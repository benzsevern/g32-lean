import HodgeLean.Foundations.Program.SchoenTowerL1bActionLogLifts
import Mathlib.Tactic.Linarith

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- An exponential return whose imaginary displacement is within one full
turn of the positive primitive turn is exactly that primitive deck return. -/
theorem s2v_l1b_action_primitive_deck_return
    (z w : ℂ) (he : Complex.exp w = Complex.exp z)
    (hnear : |(w - z).im - 2 * Real.pi| < 2 * Real.pi) :
    w = z + 2 * Real.pi * Complex.I := by
  obtain ⟨k, hk⟩ := Complex.exp_eq_exp_iff_exists_int.mp he
  have hd : w - z = k * (2 * Real.pi * Complex.I) := by
    rw [hk]
    ring
  have him : (w - z).im = (k : ℝ) * (2 * Real.pi) := by
    rw [hd]
    simp [Complex.mul_im]
  have hfactor : (k : ℝ) * (2 * Real.pi) - 2 * Real.pi =
      ((k : ℝ) - 1) * (2 * Real.pi) := by ring
  rw [him, hfactor, abs_mul, abs_of_pos Real.two_pi_pos] at hnear
  have habs : |(k : ℝ) - 1| < 1 :=
    (mul_lt_mul_iff_left₀ Real.two_pi_pos).mp (by simpa only [one_mul] using hnear)
  have hlo : (0 : ℝ) < k := by linarith [(abs_lt.mp habs).1]
  have hhi : (k : ℝ) < 2 := by linarith [(abs_lt.mp habs).2]
  have hklo : (0 : ℤ) < k := by exact_mod_cast hlo
  have hkhi : k < 2 := by exact_mod_cast hhi
  have hkone : k = 1 := by omega
  simpa only [hkone, Int.cast_one, one_mul] using hk

end HodgeLean.Foundations.Program
