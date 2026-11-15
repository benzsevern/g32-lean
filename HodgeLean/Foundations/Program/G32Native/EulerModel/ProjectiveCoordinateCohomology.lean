import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectivePermutationMatrix
import HodgeLean.Foundations.Program.G32Native.EulerModel.ProjectiveCoordinatePointAction

/-! # Rational cohomology of the specified actual projective coordinate isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The specified actual complex scheme coordinate isomorphism is exactly its native homogeneous permutation-matrix action. -/
theorem complexProjectiveCoordinatePoint_matrix (k : ℕ)
    (e : Equiv.Perm (Fin (k + 1))) :
    Point.continuousMap (complexProjectiveCoordinateIso e).hom =
      nativeProjectiveMatrixMap k (Equiv.Perm.permMatrix ℂ e.symm)
        (projectiveCoordinatePermutation_det k e) := by
  apply ContinuousMap.ext
  intro p
  obtain ⟨⟨v, hv⟩, rfl⟩ := surjective_vectorToComplexPoint p
  change Point.map (complexProjectiveCoordinateIso e).hom (vectorToComplexPoint v hv) = _
  rw [complexProjectiveCoordinatePoint_action, nativeProjectiveMatrixMap_point]
  simp only [Matrix.permMatrix_mulVec]

#print axioms complexProjectiveCoordinatePoint_matrix
/-- The specified actual complex projective coordinate isomorphism acts identically in every rational cohomology degree. -/
theorem complexProjectiveCoordinateIso_cohomology (k n : ℕ)
    (e : Equiv.Perm (Fin (k + 1)))
    (α : Cohomology ℚ (TopCat.of (ComplexPoint
      (Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ))))) n) :
    cohomologyMap ℚ n (TopCat.ofHom
      (Point.continuousMap (complexProjectiveCoordinateIso e).hom)) α = α := by
  rw [complexProjectiveCoordinatePoint_matrix]
  exact nativeProjectiveMatrix_cohomology k n _ (projectiveCoordinatePermutation_det k e) α

#print axioms complexProjectiveCoordinateIso_cohomology
end HodgeLean.Foundations.Program.G32Native.EulerModel
