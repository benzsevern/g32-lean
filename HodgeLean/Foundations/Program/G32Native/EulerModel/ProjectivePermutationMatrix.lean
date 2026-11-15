import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveNativeMatrix
import Mathlib.LinearAlgebra.Matrix.Permutation

/-! # The specified coordinate permutation as an invertible homogeneous complex matrix -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified homogeneous coordinate permutation has nonzero actual complex determinant. -/
theorem projectiveCoordinatePermutation_det (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) : (Equiv.Perm.permMatrix ℂ e.symm).det ≠ 0 := by
  rw [Matrix.det_permutation]
  exact_mod_cast (Units.ne_zero (Equiv.Perm.sign e.symm))

#print axioms projectiveCoordinatePermutation_det
end HodgeLean.Foundations.Program.G32Native.EulerModel
