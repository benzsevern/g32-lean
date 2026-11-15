import Mathlib.RingTheory.PowerSeries.Order
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Tactic

noncomputable section
set_option maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

/-- Cross multiplication of a binomial fraction equation computes its signed
series order, without requiring either numerator to be a unit. -/
theorem s2v_l1b_local_fraction_order
    {K : Type*} [Field K] (F G A B : PowerSeries K)
    (hF : F ≠ 0) (hG : G ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (m : ℕ) (hbin : F ^ m * B = A * G ^ m) :
    (m : ℤ) * ((F.order.toNat : ℤ) - (G.order.toNat : ℤ)) =
      (A.order.toNat : ℤ) - (B.order.toNat : ℤ) := by
  have hh := congrArg PowerSeries.order hbin
  rw [PowerSeries.order_mul, PowerSeries.order_mul,
    PowerSeries.order_pow, PowerSeries.order_pow] at hh
  rw [← PowerSeries.coe_toNat_order hF, ← PowerSeries.coe_toNat_order hG,
    ← PowerSeries.coe_toNat_order hA, ← PowerSeries.coe_toNat_order hB] at hh
  simp only [nsmul_eq_mul, ← Nat.cast_mul, ← Nat.cast_add] at hh
  have hh' : m * F.order.toNat + B.order.toNat =
      A.order.toNat + m * G.order.toNat := by
    exact_mod_cast hh
  have hh'' : (m : ℤ) * F.order.toNat + B.order.toNat =
      A.order.toNat + (m : ℤ) * G.order.toNat := by
    exact_mod_cast hh'
  linarith

end HodgeLean.Foundations.Program
