import Mathlib.Data.Int.GCD
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Removing the common divisor of the cover degree and signed valuation
gives positive inertia data and a coprime signed local exponent. -/
theorem s2v_l1b_local_inertia_arithmetic
    (m : ℕ) (hm : m ≠ 0) (d : ℤ) :
    ∃ e q : ℕ, ∃ n : ℤ, 0 < e ∧ 0 < q ∧
      m = e * q ∧ d = n * (q : ℤ) ∧ Int.gcd n (e : ℤ) = 1 := by
  have hmZ : (m : ℤ) ≠ 0 := by exact_mod_cast hm
  obtain ⟨q, a, n, hq, hcop, hma, hdn⟩ :=
    Int.exists_gcd_one' (Int.gcd_pos_of_ne_zero_left d hmZ)
  have hapos : 0 < a := by
    have hmpos : 0 < (m : ℤ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hqpos : 0 < (q : ℤ) := by exact_mod_cast hq
    nlinarith
  lift a to ℕ using hapos.le with e he
  refine ⟨e, q, n, ?_, hq, ?_, hdn, ?_⟩
  · exact_mod_cast hapos
  · exact_mod_cast hma
  · simpa only [Int.gcd_comm] using hcop

end HodgeLean.Foundations.Program
