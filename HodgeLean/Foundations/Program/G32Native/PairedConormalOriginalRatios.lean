import HodgeLean.Foundations.Program.G32Native.PairedConormalIntegralRatios

/-! # Exact original regular ratios under the polynomial projective isomorphism -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The regular original coordinate ratio obtained from its universal homogeneous fraction. -/
def conormalOriginalCoordinateRatio (k : ℕ) (i j : Fin (k + 1)) :
    Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ), projectiveSpaceBasicOpen k (X i)) :=
  (pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k)))).appLE
    (Proj.basicOpen (UniversalGrading k) (X i)) (projectiveSpaceBasicOpen k (X i)) le_rfl
    (Proj.awayToSection (UniversalGrading k) (X i) (chartCoordinate i j))

/-- The specified projective comparison pulls the actual original regular ratio
back to the native regular ratio with exactly the same two coordinate indices. -/
theorem conormal_original_coordinate_ratio_pullback (k : ℕ) (i j : Fin (k + 1)) :
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom.appLE
      (projectiveSpaceBasicOpen k (X i)) (ProjSpace.standardOpen ℂ k i)
      (by rw [conormal_polynomialProjectiveSpaceIso_preimage_coordinate])
      (conormalOriginalCoordinateRatio k i j) = ProjSpace.coordinateRatioSection ℂ k i j := by
  have hmap : (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ≫
      pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k))) =
      Proj.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1)))
        (s2_polynomialIntegralCoordinates_irrelevant ℂ (Fin (k + 1))) := by
    simp only [s2_polynomialProjectiveSpaceIso, asIso_hom, Category.assoc,
      pullback.map, pullback.lift_snd, Category.comp_id, b54_relativeProj, pullback.lift_snd]
  have hc := Scheme.Hom.appLE_comp_appLE
    (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom
    (pullback.snd (terminal.from (Spec ↧ℂ)) (terminal.from (Proj (UniversalGrading k))))
    (Proj.basicOpen (UniversalGrading k) (X i)) (projectiveSpaceBasicOpen k (X i))
    (ProjSpace.standardOpen ℂ k i) le_rfl
    (show ProjSpace.standardOpen ℂ k i ≤
      (s2_polynomialProjectiveSpaceIso ℂ (Fin (k + 1))).hom ⁻¹ᵁ
        projectiveSpaceBasicOpen k (X i) by
      rw [conormal_polynomialProjectiveSpaceIso_preimage_coordinate])
  have hh := ConcreteCategory.congr_hom hc
    (Proj.awayToSection (UniversalGrading k) (X i) (chartCoordinate i j))
  apply hh.trans
  convert conormal_integral_coordinate_ratio k i j using 1
  congr 3
  all_goals exact hmap

end HodgeLean.Foundations.Program.G32Native
