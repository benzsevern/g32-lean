import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrixRange
import HodgeLean.Foundations.Program.SchoenCycleProjectivePoints

/-! # Actual scheme-theoretic projective points in finite matrix coordinates -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The original scheme-theoretic complex projective space is homeomorphic to its literal finite Hermitian, unit diagonal-sum and minor equation locus.
Source: s2e_projectivePointHomeomorph; properCycle_projective_matrix_coordinates_range.
HC no distance; AV milestone no distance. -/
def properCycle_projective_matrix_scheme_homeomorph (n : ℕ) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) ≃ₜ
      {M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ |
        (∀ i j, star (M i j) = M j i) ∧ (∑ i, M i i) = 1 ∧
          ∀ i j k l, M i j * M k l = M i l * M k j} :=
  (s2e_projectivePointHomeomorph n).symm.trans
    ((properCycle_projective_matrix_coordinates_closed_embedding n).isEmbedding.toHomeomorph.trans
      (Homeomorph.setCongr properCycle_projective_matrix_coordinates_range))

end HodgeLean.Foundations.QuotientDuality
