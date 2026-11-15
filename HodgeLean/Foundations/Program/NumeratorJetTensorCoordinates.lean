import HodgeLean.Foundations.Program.NumeratorJetCoordinateAlgebra

/-! # Finite rational arithmetic in the tensor product of the two sextic quotients -/

noncomputable section
namespace HodgeLean.Foundations.Program

/-- Coordinate evaluation commutes with finite sums. -/
theorem b65e_coordinateEvalQ_sum {ι : Type*} [Fintype ι]
    (u : ι → Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ ∑ a, u a c) z =
      ∑ a, b65e_coordinateEvalQ (u a) z := by
  simp only [b65e_coordinateEvalQ, Rat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- Coordinate evaluation preserves rational scalar multiplication. -/
theorem b65e_coordinateEvalQ_scale (a : ℚ) (u : Fin 6 → ℚ) (z : ℂ) :
    b65e_coordinateEvalQ (fun c ↦ a * u c) z =
      (a : ℂ) * b65e_coordinateEvalQ u z := by
  simp only [b65e_coordinateEvalQ, Rat.cast_mul, Finset.mul_sum, mul_assoc]

/-- Evaluation of a rational tensor-coordinate array. -/
def b65e_tensorCoordinateEvalQ (u : Fin 6 → Fin 6 → ℚ) (x y : ℂ) : ℂ :=
  ∑ a : Fin 6, x ^ (a : ℕ) * b65e_coordinateEvalQ (u a) y

/-- Tensor-coordinate multiplication, reducing first in the source and then in the target. -/
def b65e_tensorCoordinateMulQ (e d : Fin 2)
    (u v : Fin 6 → Fin 6 → ℚ) (c h : Fin 6) : ℚ :=
  ∑ a : Fin 6, ∑ b : Fin 6,
    b65e_powerReductionCoeffQ ⟨a.val + b.val, by omega⟩ e c *
      b65e_coordinateMulQ d (u a) (v b) h

/-- Finite tensor-coordinate multiplication preserves evaluation at a pair of fibre roots. -/
theorem b65e_tensorCoordinateMulQ_eval (e d : Fin 2)
    (u v : Fin 6 → Fin 6 → ℚ) (x y : ℂ)
    (hx : (b65q_fibreC e).eval x = 0) (hy : (b65q_fibreC d).eval y = 0) :
    b65e_tensorCoordinateEvalQ (b65e_tensorCoordinateMulQ e d u v) x y =
      b65e_tensorCoordinateEvalQ u x y * b65e_tensorCoordinateEvalQ v x y := by
  calc
    _ = ∑ a : Fin 6, ∑ b : Fin 6,
        b65e_coordinateEvalQ
          (b65e_powerReductionCoeffQ ⟨a.val + b.val, by omega⟩ e) x *
            (b65e_coordinateEvalQ (u a) y * b65e_coordinateEvalQ (v b) y) := by
      change (∑ c : Fin 6, x ^ (c : ℕ) * b65e_coordinateEvalQ
        (fun h ↦ ∑ a : Fin 6, ∑ b : Fin 6,
          b65e_powerReductionCoeffQ ⟨a.val + b.val, by omega⟩ e c *
            b65e_coordinateMulQ d (u a) (v b) h) y) = _
      simp only [b65e_coordinateEvalQ_sum, b65e_coordinateEvalQ_scale,
        b65e_coordinateMulQ_eval d _ _ y hy, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      simp only [b65e_coordinateEvalQ, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b _
      apply Finset.sum_congr rfl
      intro c _
      ring
    _ = ∑ a : Fin 6, ∑ b : Fin 6, x ^ (a.val + b.val) *
        (b65e_coordinateEvalQ (u a) y * b65e_coordinateEvalQ (v b) y) := by
      simp_rw [b65e_coordinateEval_power _ e x hx]
    _ = _ := by
      simp only [b65e_tensorCoordinateEvalQ, Finset.sum_mul, Finset.mul_sum, pow_add]
      conv_rhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring

end HodgeLean.Foundations.Program
