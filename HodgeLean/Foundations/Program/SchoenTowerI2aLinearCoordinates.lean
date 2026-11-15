import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! # Polynomial coordinates from distinct branch evaluations
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 400000
open scoped BigOperators
namespace HodgeLean.Foundations.Program

/-- Substitution by the rows of a matrix on polynomial coordinate variables.
Source: Mathlib, MvPolynomial.aeval. -/
def s2v_i2a_matrixSubstitution
    (k : Type*) [CommRing k] (n : ℕ) (M : Matrix (Fin n) (Fin n) k) :
    MvPolynomial (Fin n) k →ₐ[k] MvPolynomial (Fin n) k :=
  MvPolynomial.aeval fun i => ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j

example (k : Type*) [CommRing k] (n : ℕ) (M : Matrix (Fin n) (Fin n) k) (i : Fin n) :
    s2v_i2a_matrixSubstitution k n M (MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j := MvPolynomial.aeval_X _ _

/-- Composition of polynomial linear substitutions follows matrix multiplication in the coefficient order.
Source: Mathlib, MvPolynomial.algHom_ext and Matrix.mul_apply. -/
theorem s2v_i2a_matrixSubstitution_comp
    (k : Type*) [CommRing k] (n : ℕ) (M N : Matrix (Fin n) (Fin n) k) :
    (s2v_i2a_matrixSubstitution k n M).comp (s2v_i2a_matrixSubstitution k n N) =
      s2v_i2a_matrixSubstitution k n (N * M) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp only [AlgHom.comp_apply, s2v_i2a_matrixSubstitution, MvPolynomial.aeval_X,
    map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply]
  simp_rw [Finset.mul_sum, ← mul_assoc, ← MvPolynomial.C_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_mul]

/-- The identity matrix induces the identity polynomial coordinate map.
Source: Mathlib, MvPolynomial.algHom_ext and Matrix.one_apply. -/
theorem s2v_i2a_matrixSubstitution_one
    (k : Type*) [CommRing k] (n : ℕ) :
    s2v_i2a_matrixSubstitution k n 1 = AlgHom.id k (MvPolynomial (Fin n) k) := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [s2v_i2a_matrixSubstitution, Matrix.one_apply]

/-- An invertible matrix gives an automorphism of the polynomial coordinates.
Source: Mathlib, Matrix.nonsing_inv_mul, Matrix.mul_nonsing_inv and AlgEquiv.ofAlgHom. -/
def s2v_i2a_matrixCoordinateEquiv
    (k : Type*) [Field k] (n : ℕ) (M : Matrix (Fin n) (Fin n) k)
    (hM : IsUnit M.det) : MvPolynomial (Fin n) k ≃ₐ[k] MvPolynomial (Fin n) k :=
  AlgEquiv.ofAlgHom (s2v_i2a_matrixSubstitution k n M)
    (s2v_i2a_matrixSubstitution k n M⁻¹)
    (by rw [s2v_i2a_matrixSubstitution_comp, Matrix.nonsing_inv_mul M hM,
      s2v_i2a_matrixSubstitution_one])
    (by rw [s2v_i2a_matrixSubstitution_comp, Matrix.mul_nonsing_inv M hM,
      s2v_i2a_matrixSubstitution_one])

example (k : Type*) [Field k] (n : ℕ) (M : Matrix (Fin n) (Fin n) k)
    (hM : IsUnit M.det) (i : Fin n) :
    s2v_i2a_matrixCoordinateEquiv k n M hM (MvPolynomial.X i) =
      ∑ j, MvPolynomial.C (M i j) * MvPolynomial.X j := MvPolynomial.aeval_X _ _

end HodgeLean.Foundations.Program
