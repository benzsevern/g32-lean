import HodgeLean.Foundations.Program.G32Native.PairedConormalOriginalIdealGenerators

/-! # Regularity of the exact original normalized ideal generator -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
open AlgebraicGeometry.ComplexProjectiveSpace
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native

/-- The literal normalized ratio is regular in its actual original Cartier chart ring. -/
theorem conormal_original_hyperplane_generator_regular (k : ℕ) (i : Fin (k + 1)) :
    IsRegular (conormalOriginalHyperplaneGenerator k i) := by
  letI : IsDomain Γ(ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ),
      (paired_hyperplaneChartOpen k i).1) :=
    (paired_hyperplaneChartSectionEquiv k i).isDomain_iff.mpr inferInstance
  apply isRegular_iff_ne_zero.mpr
  intro h
  apply paired_hyperplaneChartEquation_ne_zero k i
  have hh := congrArg (paired_hyperplaneChartSectionEquiv k i) h
  simpa only [conormal_original_hyperplane_generator_coordinate, map_zero] using hh

/-- The exact original ratio is regular in every affine presentation of its coordinate open. -/
theorem conormal_original_hyperplane_generator_regular_on_coordinate
    (k : ℕ) (i : Fin (k + 1))
    (U : (ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).affineOpens)
    (hU : U.1 = projectiveSpaceBasicOpen k (X i)) :
    IsRegular ((ProjectiveSpace (Fin (k + 1)) (Spec ↧ℂ)).presheaf.map
      (homOfLE hU.le).op (conormalOriginalCoordinateRatio k i 0)) := by
  have hUc : U = paired_hyperplaneChartOpen k i :=
    Subtype.ext (hU.trans (conormal_hyperplane_chartOpen_eq_coordinate k i).symm)
  subst U
  exact conormal_original_hyperplane_generator_regular k i

end HodgeLean.Foundations.Program.G32Native
