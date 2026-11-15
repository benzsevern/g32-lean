import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveBooleanModel

/-! # Actual homogeneous values of the scheme projective Boolean model -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- On an original homogeneous vector, the scheme projective Boolean homeomorphism is its actual normalized outer product in Euclidean coordinates.
Source: projectivizationToComplexPoint_mk; s2e_projectivePointHomeomorph.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_boolean_vector (n : ℕ) (v : CoordinateSpace n) (hv : v ≠ 0) :
    (properCycle_projective_boolean_homeomorph n (vectorToComplexPoint v hv)).val =
      properCycle_matrix_euclidean_coordinates (properCycle_projective_matrix v) := by
  have he : s2e_projectivePointHomeomorph n (Projectivization.mk ℂ v hv) =
      vectorToComplexPoint v hv := rfl
  change properCycle_matrix_euclidean_coordinates (properCycle_projective_matrix_coordinates
    ((s2e_projectivePointHomeomorph n).symm (vectorToComplexPoint v hv))) = _
  rw [← he, Homeomorph.symm_apply_apply]
  rfl

/-- The original affine projective chart has its actual coordinate-updated matrix value in the Boolean model.
Source: s2e_projective_affineChart_vector; properCycle_projective_boolean_vector.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_boolean_affine_chart (n : ℕ) (i : Fin (n+1))
    (z : ComplexPoint (Over.mk (AlgebraicGeometry.ComplexPoint.complexAffineSpace (Fin (n+1)) ↘ Spec ↧ℂ))) :
    (properCycle_projective_boolean_homeomorph n (chartAffineComplexPointMap i z)).val =
      properCycle_matrix_euclidean_coordinates (properCycle_projective_matrix
        (Function.update (AlgebraicGeometry.ComplexPoint.affineSpaceEquiv (Fin (n+1)) z) i 1)) := by
  have he := s2e_projective_affineChart_vector i
    (AlgebraicGeometry.ComplexPoint.affineSpaceEquiv (Fin (n+1)) z)
  rw [Equiv.symm_apply_apply] at he
  rw [he, properCycle_projective_boolean_vector]

end HodgeLean.Foundations.QuotientDuality
