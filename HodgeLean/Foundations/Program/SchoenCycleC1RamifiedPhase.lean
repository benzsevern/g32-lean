import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- The exact ramification order equation transports the signed native
rotation phase to the original covering degree. -/
theorem s2e_c1_ramified_rotation_phase
    (m e : ℕ) (hm : 0 < m) (he : 0 < e) (ε r n : ℤ)
    (hrel : (m : ℤ) * r = (e : ℤ) * n) :
    Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (e : ℂ)) ^ r =
      Complex.exp (2 * Real.pi * Complex.I / (m : ℂ)) ^ (ε * n) := by
  rw [← Complex.exp_int_mul, ← Complex.exp_int_mul]
  congr 1
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have heC : (e : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt he)
  have hrelC : (m : ℂ) * (r : ℂ) = (e : ℂ) * (n : ℂ) := by exact_mod_cast hrel
  push_cast
  field_simp
  linear_combination (ε : ℂ) * hrelC

end HodgeLean.Foundations.Program
