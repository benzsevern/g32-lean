import HodgeLean.Foundations.Abdulali.SkewTrace
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Trace

noncomputable section
namespace HodgeLean.Foundations.Abdulali
variable {n : ℕ}

/-- The intrinsic skew equation equals its matrix equation in the function basis.
Source: Humphreys, Linear Algebraic Groups, §13.1, classical Lie algebras. -/
theorem skew_iff_matrix (B : LinearMap.BilinForm ℂ (Fin n → ℂ))
    (X : Module.End ℂ (Fin n → ℂ)) :
    (∀ u v, B (X u) v + B u (X v) = 0) ↔
      (LinearMap.toMatrix' X).transpose * LinearMap.toMatrix₂' ℂ B +
        LinearMap.toMatrix₂' ℂ B * LinearMap.toMatrix' X = 0 := by
  let F := B.compl₁₂ X LinearMap.id + B.compl₁₂ LinearMap.id X
  have hm : LinearMap.toMatrix₂' ℂ F =
      (LinearMap.toMatrix' X).transpose * LinearMap.toMatrix₂' ℂ B +
        LinearMap.toMatrix₂' ℂ B * LinearMap.toMatrix' X := by
    simp only [F, map_add, LinearMap.toMatrix₂'_compl₁₂, LinearMap.toMatrix'_id,
      Matrix.transpose_one, mul_one, one_mul]
  have hf : (∀ u v, B (X u) v + B u (X v) = 0) ↔ F = 0 := by
    constructor
    · intro h
      apply LinearMap.ext
      intro u
      apply LinearMap.ext
      intro v
      exact h u v
    · intro h u v
      exact congrArg (fun G : LinearMap.BilinForm ℂ (Fin n → ℂ) => G u v) h
  rw [hf, ← hm]
  exact (LinearMap.toMatrix₂' ℂ).map_eq_zero_iff.symm

/-- The intrinsic skew equation for a nondegenerate form forces zero trace.
Source: Humphreys, Linear Algebraic Groups, §13.1, classical Lie algebras. -/
theorem trace_eq_zero_of_bilinear_skew (B : LinearMap.BilinForm ℂ (Fin n → ℂ))
    (hB : B.Nondegenerate) (X : Module.End ℂ (Fin n → ℂ))
    (hX : ∀ u v, B (X u) v + B u (X v) = 0) : LinearMap.trace ℂ _ X = 0 := by
  have hdet : IsUnit (LinearMap.toMatrix₂' ℂ B).det := by
    apply isUnit_iff_ne_zero.mpr
    apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
    change (Matrix.toBilin' (LinearMap.BilinForm.toMatrix' B)).Nondegenerate
    rw [Matrix.toBilin'_toMatrix']
    exact hB
  have ht := trace_eq_zero_of_skew _ _ hdet ((skew_iff_matrix B X).mp hX)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basisFun ℂ (Fin n))]
  exact ht

#print axioms skew_iff_matrix
#print axioms trace_eq_zero_of_bilinear_skew
end HodgeLean.Foundations.Abdulali
