import HodgeLean.Foundations.Program.G32Native.PairedConormalNativeRowZero
import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialChartPoint

/-! # Actual fibre row vanishing detected by its original polynomial numerator -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial AlgebraicGeometry.ComplexProjectiveSpace
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- At the same actual evaluation point, a normalized native ideal row vanishes
on the fibre exactly when its specified homogeneous polynomial numerator vanishes. -/
theorem conormal_polynomial_ideal_row_pullback_zero_iff (k : ℕ)
    (φ : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit (Proj (homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (p : homogeneousSubmodule (Fin (k + 1)) ℂ 1)
    (hp : ∀ j : Fin (k + 1),
      conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k) φ
        (conormalNativeCoordinateOpen ℂ k j) (ProjSpace.coordinateRatioSection ℂ k j 0)
        (conormal_native_hyperplane_coordinate_mem ℂ k j) =
          ProjSpace.homogeneousRatioSection ℂ k 1 p j)
    (v : CoordinateSpace k) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    (Scheme.Modules.pullback (conormalPolynomialChartComplexPoint v i hi).left).map φ = 0 ↔
      eval v p.val = 0 := by
  rw [conormal_native_ideal_row_pullback_zero_iff k i φ
    (conormalPolynomialChartComplexPoint v i hi) (conormal_polynomial_chart_complex_point_mem v i hi)]
  rw [hp i]
  change Point.evaluate (ProjSpace.standardOpen ℂ k i)
    (ProjSpace.homogeneousRatioSection ℂ k 1 p i) (conormalPolynomialChartComplexPoint v i hi) = 0 ↔ _
  rw [conormal_polynomial_chart_complex_point_evaluate v i hi 1 p]
  simp only [pow_one, mul_eq_zero, inv_eq_zero, or_iff_left hi]

end HodgeLean.Foundations.Program.G32Native
