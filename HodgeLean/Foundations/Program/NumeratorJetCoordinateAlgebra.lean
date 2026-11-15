import HodgeLean.Foundations.Program.NumeratorJetPowerMoments

/-! # Finite rational arithmetic in the sextic coordinates -/

noncomputable section
open Polynomial
namespace HodgeLean.Foundations.Program

/-- Evaluation of a six-coordinate rational array. -/
def b65e_coordinateEvalQ (u : Fin 6 → ℚ) (z : ℂ) : ℂ :=
  ∑ c : Fin 6, (u c : ℂ) * z ^ (c : ℕ)

/-- Multiplication of rational coordinate arrays using the checked monomial reductions. -/
def b65e_coordinateMulQ (e : Fin 2) (u v : Fin 6 → ℚ) (c : Fin 6) : ℚ :=
  ∑ a : Fin 6, ∑ b : Fin 6,
    u a * v b * b65e_powerReductionCoeffQ ⟨a.val + b.val, by omega⟩ e c

/-- Reduced monomial coordinates evaluate to the corresponding power. -/
theorem b65e_coordinateEval_power (n : Fin 11) (e : Fin 2) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    b65e_coordinateEvalQ (b65e_powerReductionCoeffQ n e) z = z ^ (n : ℕ) := by
  rw [← b65e_powerReduction_eval n e z hz]
  simp only [b65e_powerReductionQ, b65e_ofFn_eq_sum, eval₂_finsetSum,
    eval₂_mul, eval₂_C, eval₂_pow, eval₂_X, Rat.coe_castHom, b65e_coordinateEvalQ]

/-- Coordinate multiplication preserves evaluation on every root of the sextic. -/
theorem b65e_coordinateMulQ_eval (e : Fin 2) (u v : Fin 6 → ℚ) (z : ℂ)
    (hz : (b65q_fibreC e).eval z = 0) :
    b65e_coordinateEvalQ (b65e_coordinateMulQ e u v) z =
      b65e_coordinateEvalQ u z * b65e_coordinateEvalQ v z := by
  calc
    _ = ∑ a : Fin 6, ∑ b : Fin 6, (u a : ℂ) * (v b : ℂ) *
        b65e_coordinateEvalQ
          (b65e_powerReductionCoeffQ ⟨a.val + b.val, by omega⟩ e) z := by
      simp only [b65e_coordinateEvalQ, b65e_coordinateMulQ]
      push_cast
      simp only [Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = ∑ a : Fin 6, ∑ b : Fin 6, (u a : ℂ) * (v b : ℂ) * z ^ (a.val + b.val) := by
      simp_rw [b65e_coordinateEval_power _ e z hz]
    _ = _ := by
      simp only [b65e_coordinateEvalQ, Finset.sum_mul, Finset.mul_sum, pow_add]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

end HodgeLean.Foundations.Program
