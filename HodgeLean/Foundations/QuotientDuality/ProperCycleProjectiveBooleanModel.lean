import HodgeLean.Foundations.QuotientDuality.ProperCycleMatrixRealCoordinates
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveMatrixSchemeModel

/-! # Actual compact Boolean models of scheme-theoretic complex projective space -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
open scoped BigOperators
namespace HodgeLean.Foundations.QuotientDuality

/-- The projective matrix locus has an explicit real Boolean formula in its original Euclidean matrix coordinates.
Source: properCycle_polynomial_matrix_formula; properCycle_matrix_euclidean_coordinates.
HC no distance; AV milestone no distance. -/
def properCycle_projective_matrix_real_formula (ι : Type) [Fintype ι] :
    s2v_t11b_Formula (Fintype.card ((ι × ι) ⊕ (ι × ι))) :=
  properCycle_polynomial_matrix_formula
    (fun i j => MvPolynomial.X (Fintype.equivFin _ (Sum.inl (i,j))))
    (fun i j => MvPolynomial.X (Fintype.equivFin _ (Sum.inr (i,j))))

/-- The real Boolean formula retains exactly the original complex matrix equations.
Source: properCycle_polynomial_matrix_formula_iff; properCycle_matrix_euclidean_coordinates_eval.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_matrix_real_formula_iff {ι : Type} [Fintype ι]
    (M : Matrix ι ι ℂ) :
    properCycle_matrix_euclidean_coordinates M ∈
      (properCycle_projective_matrix_real_formula ι).realize ↔
        (∀ i j, star (M i j) = M j i) ∧ (∑ i, M i i) = 1 ∧
          ∀ i j k l, M i j * M k l = M i l * M k j := by
  unfold properCycle_projective_matrix_real_formula
  rw [properCycle_polynomial_matrix_formula_iff]
  simp only [MvPolynomial.eval_X, properCycle_matrix_euclidean_coordinates_eval]
  rfl

/-- Original scheme-theoretic projective points retain an actual Euclidean Boolean carrier homeomorphism.
Source: properCycle_projective_matrix_scheme_homeomorph; properCycle_projective_matrix_real_formula_iff.
HC no distance; AV milestone no distance. -/
def properCycle_projective_boolean_homeomorph (n : ℕ) :
    ComplexPoint (Over.mk (ProjectiveSpace.toBase (Fin (n + 1)) (Spec ↧ℂ))) ≃ₜ
      (properCycle_projective_matrix_real_formula (Fin (n + 1))).realize :=
  (properCycle_projective_matrix_scheme_homeomorph n).trans
    (properCycle_matrix_euclidean_coordinates.sets (by
      ext M
      exact (properCycle_projective_matrix_real_formula_iff M).symm))

/-- The literal Boolean projective carrier is compact in its original Euclidean ambient space.
Source: ComplexPoint.instCompactSpace_of_isProper; properCycle_projective_boolean_homeomorph.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_boolean_compact (n : ℕ) :
    IsCompact (properCycle_projective_matrix_real_formula (Fin (n + 1))).realize := by
  letI := (properCycle_projective_boolean_homeomorph n).compactSpace
  exact isCompact_iff_compactSpace.mpr inferInstance

end HodgeLean.Foundations.QuotientDuality
