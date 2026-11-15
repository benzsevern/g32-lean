import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Complex.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.Matrix.Trace

noncomputable section
namespace HodgeLean.Foundations.Abdulali
variable {n : ℕ}

/-- A skew operator for an invertible complex Gram matrix has zero trace.
No symmetry assumption on the Gram matrix is required.
Source: Humphreys, Linear Algebraic Groups, §13.1, classical Lie algebras. -/
theorem trace_eq_zero_of_skew (Ω X : Matrix (Fin n) (Fin n) ℂ)
    (hΩ : IsUnit Ω.det) (hX : X.transpose * Ω + Ω * X = 0) : X.trace = 0 := by
  have he : Ω⁻¹ * (X.transpose * Ω) = -X := by
    rw [add_eq_zero_iff_eq_neg] at hX
    rw [hX, mul_neg, Matrix.nonsing_inv_mul_cancel_left _ _ hΩ]
  have ht : (Ω⁻¹ * (X.transpose * Ω)).trace = X.trace := by
    rw [Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hΩ,
      mul_one, Matrix.trace_transpose]
  rw [he, Matrix.trace_neg] at ht
  linear_combination -(1/2 : ℂ) * ht

#print axioms trace_eq_zero_of_skew
end HodgeLean.Foundations.Abdulali
