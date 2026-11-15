import HodgeLean.Foundations.Program.G32Native.FixedEquationCoordinates
import HodgeLean.Foundations.Program.G32Native.FixedPeriodDerivative
import HodgeLean.Foundations.Program.G32Native.CanonicalConormalKernel
import HodgeLean.Foundations.Program.G32Native.FiniteCoordinateKernel

/-! # Kernel control for the original fixed-chart period differential -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Filter Topology
open HodgeLean.Foundations.Curves.Picard.LineBundles
open scoped Manifold ContDiff
namespace HodgeLean.Foundations.Program.G32Native

/-- Wherever the fixed equation matrix is surjective, its kernel is contained
in the kernel of the coherent original fixed period derivative. -/
theorem fixedPeriodDerivative_ker_le (G : CanonicalAbelGeometry)
    (F : ComplexPoint G.Q → (Fin (G.k + G.k) → ℂ) → (Fin (G.k + 1) → ℂ))
    (x : ComplexPoint G.Q) (U : G.W.left.Opens)
    (s : Fin G.k → (unit U.toScheme ⟶
      (Scheme.Modules.pullback U.ι).obj (Conormal.idealModule G.ι.left)))
    (y : ComplexPoint G.Q) (hyU : Point.map G.ι y ∈ Point.overOpen U)
    (hyp : Point.map G.ι y ∈ (localChart G.W (G.k + G.k) (Point.map G.ι x)).source)
    (hx : AnalyticAt ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)))
    (hy : AnalyticAt ℂ (F y)
      (localChart G.W (G.k + G.k) (Point.map G.ι y) (Point.map G.ι y)))
    (hq : (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F x w))
      =ᶠ[𝓝 (Point.map G.ι y)]
      (fun w => canonicalPeriodQuotient G (canonicalChartAbelLift G F y w)))
    (hgeom : LinearMap.ker (canonicalAbelDifferential G F y) = LinearMap.range
      (fderiv ℂ (inclusionInComplexCharts G.W G.Q G.ι G.k (G.k + G.k) y)
        (localChart G.Q G.k y y)).toLinearMap)
    (hA : Function.Surjective (equationFixedDerivative G x U s y)) :
    LinearMap.ker (equationFixedDerivative G x U s y).toLinearMap ≤
      LinearMap.ker (fderiv ℂ (F x)
        (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))).toLinearMap := by
  letI := smoothNormalPoint_finiteDimensional G.Q G.W G.k G.k G.ι y
  refine ker_le_of_surjective_normal_coordinates (canonicalConormalDerivative G y)
    (equationPointCoordinates G U s y hyU)
    (fixedToPointTangent G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y)).toLinearMap
    (equationFixedDerivative G x U s y).toLinearMap
    ((coefficientCoordinateEquiv G.k).toLinearMap.comp (canonicalAbelDifferential G F y))
    (fderiv ℂ (F x)
      (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι y))).toLinearMap
    (equationFixedDerivative_factor G x U s y hyU hyp)
    (fixedPeriodDerivative_factor G F x y hyp hx hy hq) ?_ hA ?_
  · exact (smoothNormalPoint_finrank G.Q G.W G.k G.k G.ι y).trans
      (Module.finrank_fin_fun (n := G.k) ℂ).symm
  · intro w hw
    have ht := (canonicalConormalDerivative_ker G y).le hw
    have hz : canonicalAbelDifferential G F y w = 0 := hgeom.symm.le ht
    change coefficientCoordinateEquiv G.k (canonicalAbelDifferential G F y w) = 0
    rw [hz, map_zero]

#print axioms fixedPeriodDerivative_ker_le
end HodgeLean.Foundations.Program.G32Native
