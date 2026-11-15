import HodgeLean.Foundations.Program.G32Native.PairedConormalNativePointScalars
import HodgeLean.Foundations.Program.G32Native.PairedConormalPolynomialChartPoint
import HodgeLean.Foundations.Program.G32Native.EulerModel.NormalProjectiveScheme

/-! # Exact polynomial coordinates of the normalized actual relation vector -/

noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program HodgeLean.Foundations.Curves.Picard.LineBundles
attribute [local instance] MvPolynomial.gradedAlgebra

/-- All coordinates of the actual normalized relation are the original
homogeneous polynomial values with the same single denominator scalar. -/
theorem conormal_native_point_relation_polynomial_coordinates (k : ℕ)
    (a : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.unit
        (Proj (homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf)
    (b : idealModule (conormalNativeHyperplaneIdeal ℂ k) ⟶
      SheafOfModules.free
        (R := (Proj (homogeneousSubmodule (Fin (k + 1)) ℂ)).ringCatSheaf) (Fin k))
    (p : Fin (k + 1) → homogeneousSubmodule (Fin (k + 1)) ℂ 1)
    (hp : ∀ (r i : Fin (k + 1)),
      conormalIdealMapCoefficient (conormalNativeHyperplaneIdeal ℂ k)
        (Fin.cases a (fun t => b ≫ HodgeLean.Foundations.BundleThom.i1_freeSheafProjection
          (Proj (homogeneousSubmodule (Fin (k + 1)) ℂ)) k t) r)
        (conormalNativeCoordinateOpen ℂ k i) (ProjSpace.coordinateRatioSection ℂ k i 0)
        (conormal_native_hyperplane_coordinate_mem ℂ k i) =
          ProjSpace.homogeneousRatioSection ℂ k 1 (p r) i)
    (v : Fin (k + 1) → ℂ) (i : Fin (k + 1)) (hi : v i ≠ 0) :
    let x := conormalPolynomialChartComplexPoint v i hi
    let hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1 :=
      conormal_polynomial_chart_complex_point_mem v i hi
    EulerModel.normalHomogeneousCoordinates k
      (conormalPointRelationVector k a b x.left (conormalNativeIdealPointFrame k i x hx)) =
        (v i)⁻¹ • (fun r => eval v (p r).val) := by
  dsimp only
  let x := conormalPolynomialChartComplexPoint v i hi
  let hx : x ∈ Point.overOpen (conormalNativeCoordinateOpen ℂ k i).1 :=
    conormal_polynomial_chart_complex_point_mem v i hi
  funext r
  refine Fin.cases ?_ (fun t => ?_) r
  · change (conormalPointRelationVector k a b x.left
        (conormalNativeIdealPointFrame k i x hx)).1 = (v i)⁻¹ * eval v (p 0).val
    have hp0 := hp 0 i
    simp only [Fin.cases_zero] at hp0
    rw [conormal_native_point_relation_vector_fst]
    erw [hp0]
    change Point.evaluate (ProjSpace.standardOpen ℂ k i)
      (ProjSpace.homogeneousRatioSection ℂ k 1 (p 0) i)
      (conormalPolynomialChartComplexPoint v i hi) = _
    rw [conormal_polynomial_chart_complex_point_evaluate]
    simp only [pow_one, mul_comm]
  · change (conormalPointRelationVector k a b x.left
        (conormalNativeIdealPointFrame k i x hx)).2 t = (v i)⁻¹ * eval v (p t.succ).val
    have hpt := hp t.succ i
    simp only [Fin.cases_succ] at hpt
    rw [conormal_native_point_relation_vector_row]
    erw [hpt]
    change Point.evaluate (ProjSpace.standardOpen ℂ k i)
      (ProjSpace.homogeneousRatioSection ℂ k 1 (p t.succ) i)
      (conormalPolynomialChartComplexPoint v i hi) = _
    rw [conormal_polynomial_chart_complex_point_evaluate]
    simp only [pow_one, mul_comm]

#print axioms conormal_native_point_relation_polynomial_coordinates
end HodgeLean.Foundations.Program.G32Native
