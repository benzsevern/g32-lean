import HodgeLean.Foundations.Program.SchoenPolynomialProjectiveSpace
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveHausdorff

/-! # Original homogeneous coordinate opens under the polynomial projective comparison -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program AlgebraicGeometry.ComplexProjectiveSpace
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual polynomial projective comparison preserves each specified homogeneous coordinate open. -/
theorem conormal_polynomialProjectiveSpaceIso_preimage_coordinate (k : ℕ) (i : Fin (k + 1)) :
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ⁻¹ᵁ
      projectiveSpaceBasicOpen k (X i) =
    Proj.basicOpen (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) := by
  unfold projectiveSpaceBasicOpen
  rw [← Scheme.Hom.comp_preimage]
  have hmap : (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
      pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k))) =
      Proj.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)))
        (s2_polynomialIntegralCoordinates_irrelevant ℂ (Fin (k + 1))) := by
    simp only [s2_polynomialProjectiveSpaceIso, asIso_hom, Category.assoc,
      pullback.map, pullback.lift_snd, Category.comp_id, b54_relativeProj, pullback.lift_snd]
  rw [hmap, Proj.map_preimage_basicOpen, s2_polynomialIntegralCoordinates_X]

end HodgeLean.Foundations.Program.G32Native
