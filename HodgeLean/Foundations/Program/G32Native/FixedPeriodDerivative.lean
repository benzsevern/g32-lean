import HodgeLean.Foundations.Program.G32Native.CoherentPeriodChartDerivatives
import HodgeLean.Foundations.Program.G32Native.CoefficientCoordinateEquiv
import HodgeLean.Foundations.Program.G32Native.FixedChartTangentMaps

/-! # Fixed-chart expressions of the original period derivative -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- The original ordered coefficient derivative in the point chart is the
fixed lift derivative on the transported original tangent vector. -/
theorem coefficientPointDerivative_fixedChart (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x y : ComplexPoint G.Q)
    (hyp : Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source)
    (hx : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))
    (hy : AnalyticAt ℂ (F y)
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)))
    (hq : (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
      =ᶠ[𝓝 (Point.map G.ι y)]
      (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w))) :
    (coefficientCoordinateEquiv G.k).toLinearMap.comp (canonicalAbelDifferential G F y) =
      (fderiv ℂ (F x)
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))).toLinearMap.comp
        (pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)).toLinearMap := by
  have hd := canonicalAbelDifferential_fixedChart G F x y hyp hx hy hq
  apply LinearMap.ext
  intro v
  change coefficientCoordinateEquiv G.k (canonicalAbelDifferential G F y v) = _
  rw [hd]
  exact coefficientCoordinateEquiv_coefficientDual G.k _

#print axioms coefficientPointDerivative_fixedChart

/-- The fixed period derivative factors through the original point
coefficient differential and the inverse tangent change. -/
theorem fixedPeriodDerivative_factor (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x y : ComplexPoint G.Q)
    (hyp : Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source)
    (hx : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))
    (hy : AnalyticAt ℂ (F y)
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)))
    (hq : (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
      =ᶠ[𝓝 (Point.map G.ι y)]
      (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w))) :
    (fderiv ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))).toLinearMap =
    ((coefficientCoordinateEquiv G.k).toLinearMap.comp (canonicalAbelDifferential G F y)).comp
      (fixedToPointTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)).toLinearMap := by
  let I := pointToFixedTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)
  let J := fixedToPointTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)
  apply LinearMap.ext
  intro v
  have hIJ : I (J v) = v := DFunLike.congr_fun
    (pointToFixed_comp_fixedToPoint G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y) hyp) v
  have hh := DFunLike.congr_fun (coefficientPointDerivative_fixedChart G F x y hyp hx hy hq) (J v)
  change coefficientCoordinateEquiv G.k (canonicalAbelDifferential G F y (J v)) =
    (fderiv ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))) (I (J v)) at hh
  change (fderiv ℂ (F x)
    (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))) v = _
  rw [hIJ] at hh
  exact hh.symm

#print axioms fixedPeriodDerivative_factor

end HodgeLean.Foundations.Program.G32Native
