import HodgeLean.Foundations.QuotientDuality.MonomialResidueWeights
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Ring.Divisibility.Basic

/-! Exact covering multiples for the residue weights of a complementary pair. -/
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.QuotientDuality

theorem paired_residue_weights_covering_multiple
    (m : ℕ) (hm : 0 < m) (a b s : ℤ) (k l : ℕ) (hpair : k + l = m)
    (ha : (m : ℤ) ∣ a - s * (k : ℤ)) (hb : (m : ℤ) ∣ b - s * (l : ℤ)) :
    ∃ q : ℕ, (a % (m : ℤ)).toNat + (b % (m : ℤ)).toNat = q * m := by
  have h := dvd_add (dvd_add ha hb) (dvd_mul_left (m : ℤ) s)
  have heq : (a - s * (k : ℤ)) + (b - s * (l : ℤ)) + s * (m : ℤ) = a + b := by
    rw [← hpair, Nat.cast_add]
    ring
  rw [heq] at h
  obtain ⟨q, hq⟩ := residue_pair_weights_divisible m hm a b h
  exact ⟨q, hq.trans (mul_comm m q)⟩

#print axioms paired_residue_weights_covering_multiple
end HodgeLean.Foundations.QuotientDuality
