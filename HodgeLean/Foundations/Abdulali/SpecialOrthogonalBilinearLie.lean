import HodgeLean.Foundations.Abdulali.SpecialOrthogonalLie
import HodgeLean.Foundations.Abdulali.SkewBilinearMatrix

noncomputable section
set_option maxHeartbeats 200000
set_option Elab.async false
namespace HodgeLean.Foundations.Abdulali
open HodgeLean.Foundations
variable {n : ℕ}

/-- The tangent condition on determinant-one isometries is precisely the
intrinsic skew condition for a nondegenerate bilinear form. The trace equation
is a consequence, rather than an additional hypothesis.
Source: Humphreys, Linear Algebraic Groups, §13.1, classical Lie algebras. -/
theorem lie_specialOrthogonalMatrixGroup_iff_bilinear_skew
    (B : LinearMap.BilinForm ℂ (Fin n → ℂ)) (hB : B.Nondegenerate)
    (X : Module.End ℂ (Fin n → ℂ)) :
    LinearMap.toMatrix' X ∈
      g1_lieAlgebra (specialOrthogonalMatrixGroup (LinearMap.toMatrix₂' ℂ B)) ↔
      ∀ u v, B (X u) v + B u (X v) = 0 := by
  rw [lie_specialOrthogonalMatrixGroup]
  constructor
  · intro h
    exact (skew_iff_matrix B X).mpr h.1
  · intro h
    have hdet : IsUnit (LinearMap.toMatrix₂' ℂ B).det := by
      apply isUnit_iff_ne_zero.mpr
      apply LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mp
      change (Matrix.toBilin' (LinearMap.BilinForm.toMatrix' B)).Nondegenerate
      rw [Matrix.toBilin'_toMatrix']
      exact hB
    have hm := (skew_iff_matrix B X).mp h
    exact ⟨hm, trace_eq_zero_of_skew _ _ hdet hm⟩

#print axioms lie_specialOrthogonalMatrixGroup_iff_bilinear_skew
end HodgeLean.Foundations.Abdulali
