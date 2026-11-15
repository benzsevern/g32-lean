import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Logic.Function.Iterate
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

noncomputable section
set_option maxHeartbeats 200000
namespace HodgeLean.Foundations.Program

/-- A lifted orbit returning by one deck transformation has rotation scalar
determined by the conjugating angle function's integral deck coefficient. -/
theorem s2v_l1b_action_lift_rotation_scalar
    {X : Type*} (f deck : X → X) (angle : X → ℝ)
    (N : ℕ) (hN : 0 < N) (ε k : ℤ) (θ : ℝ)
    (hdeck : ∀ y, angle (deck y) = angle y + ε)
    (hequiv : ∀ y, angle (f y) = angle y + θ + k)
    (x : X) (hperiod : f^[N] x = deck x) :
    Complex.exp ((θ : ℂ) * (2 * Real.pi * Complex.I)) =
      Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (N : ℂ)) := by
  have hi (n : ℕ) : angle (f^[n] x) = angle x + (n : ℝ) * (θ + k) := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hequiv, ih, Nat.cast_add, Nat.cast_one]
      ring
  have hn := hi N
  rw [hperiod, hdeck] at hn
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : θ + (k : ℝ) = (ε : ℝ) / N := (eq_div_iff hNr).mpr (by linarith)
  have hθ : θ = (ε : ℝ) / N - k := by linarith
  rw [hθ]
  simp only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_intCast,
    Complex.ofReal_natCast]
  rw [sub_mul, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]
  congr 1
  ring

/-- A logarithmic lift with an integral deck coefficient determines the
rescaling scalar of an orbit returning by one deck transformation. -/
theorem s2v_l1b_action_log_lift_rotation_scalar
    {X : Type*} (f deck : X → X) (L : X → ℂ)
    (N : ℕ) (hN : 0 < N) (ε k : ℤ) (a : ℂ)
    (hdeck : ∀ y, L (deck y) = L y + ε * (2 * Real.pi * Complex.I))
    (hequiv : ∀ y, L (f y) = L y + a + k * (2 * Real.pi * Complex.I))
    (x : X) (hperiod : f^[N] x = deck x) :
    Complex.exp a =
      Complex.exp ((ε : ℂ) * (2 * Real.pi * Complex.I) / (N : ℂ)) := by
  have hi (n : ℕ) : L (f^[n] x) =
      L x + (n : ℂ) * (a + k * (2 * Real.pi * Complex.I)) := by
    induction n with
    | zero => simp only [Function.iterate_zero_apply, Nat.cast_zero, zero_mul, add_zero]
    | succ n ih =>
      rw [Function.iterate_succ_apply', hequiv, ih, Nat.cast_add, Nat.cast_one]
      ring
  have hn := hi N
  rw [hperiod, hdeck] at hn
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hs : a + k * (2 * Real.pi * Complex.I) =
      ε * (2 * Real.pi * Complex.I) / N := (eq_div_iff hNc).mpr (by linear_combination -hn)
  have ha : a = ε * (2 * Real.pi * Complex.I) / N - k * (2 * Real.pi * Complex.I) := by
    linear_combination hs
  rw [ha, Complex.exp_sub, Complex.exp_int_mul_two_pi_mul_I, div_one]

end HodgeLean.Foundations.Program
