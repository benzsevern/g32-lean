import HodgeLean.Foundations.Program.SchoenTowerL1bActionPrimitiveDeck
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.FieldSimp

noncomputable section
set_option maxHeartbeats 200000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Small angular error at every step of a finite lifted orbit forces its
full return to be the positive primitive deck translation. -/
theorem s2v_l1b_action_primitive_return_of_orbit_error
    (f : ℂ → ℂ) (N : ℕ) (hN : 0 < N) (z : ℂ)
    (he : Complex.exp (f^[N] z) = Complex.exp z)
    (hstep : ∀ j < N,
      |(f^[j + 1] z - f^[j] z).im - (2 * Real.pi) / N| < (2 * Real.pi) / N) :
    f^[N] z = z + 2 * Real.pi * Complex.I := by
  apply s2v_l1b_action_primitive_deck_return z _ he
  let d : ℕ → ℝ := fun j => (f^[j + 1] z).im - (f^[j] z).im - (2 * Real.pi) / N
  have htel (n : ℕ) : ∑ j ∈ Finset.range n, d j =
      (f^[n] z).im - z.im - (n : ℝ) * ((2 * Real.pi) / N) := by
    induction n with
    | zero => simp only [Finset.sum_range_zero, Function.iterate_zero_apply,
        sub_self, Nat.cast_zero, zero_mul, sub_zero]
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      dsimp only [d]
      rw [Nat.cast_add, Nat.cast_one]
      ring
  have hNr : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hNN : (N : ℝ) * ((2 * Real.pi) / N) = 2 * Real.pi := by field_simp
  have hc : (∑ j ∈ Finset.range N, (2 * Real.pi) / (N : ℝ)) = 2 * Real.pi := by
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using hNN
  have hs : (∑ j ∈ Finset.range N, |d j|) < ∑ j ∈ Finset.range N, (2 * Real.pi) / (N : ℝ) :=
    Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_range.mpr hN⟩ (fun j hj => by
      simpa only [d, Complex.sub_im] using hstep j (Finset.mem_range.mp hj))
  have hb := (Finset.abs_sum_le_sum_abs d (Finset.range N)).trans_lt hs
  rw [htel, hc, hNN] at hb
  simpa only [Complex.sub_im] using hb

end HodgeLean.Foundations.Program
