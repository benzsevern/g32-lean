import HodgeLean.Foundations.Program.G32Native.ConormalPointDerivativeSurjectivity
import HodgeLean.Foundations.Program.G32Native.CanonicalAbelDifferentialDefs

/-! # Actual conormal differentiation in the retained canonical chart -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program.G32Native

/-- Original ambient tangent directions act on the retained actual dual
conormal fibre using the original chosen chart's coordinate open. -/
def canonicalConormalDerivative (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    (Fin (G.k + G.k) → ℂ) →ₗ[ℂ] canonicalNormalFibre G x := by
  let D := localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)
  have hU : IsAffineOpen D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
      using D.isAffine
  have hx : Point.map G.ι x ∈ Point.overOpen D.ambientCoordinateOpen := by
    simpa only [Point.overOpen, Set.mem_setOf_eq, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using D.mem
  exact conormalPointDerivativeMap G.ι (G.k + G.k) x D.ambientCoordinateOpen hU hx

/-- The retained original canonical tangent directions fill the actual
retained dual conormal fibre. -/
theorem canonicalConormalDerivative_surjective (G : CanonicalAbelGeometry) (x : ComplexPoint G.Q) :
    Function.Surjective (canonicalConormalDerivative G x) := by
  let D := localEtaleCoordinates G.W (G.k + G.k) (Point.map G.ι x)
  have hU : IsAffineOpen D.ambientCoordinateOpen := by
    simpa only [LocalEtaleCoordinates.ambientCoordinateOpen, Scheme.Opens.ι_image_top]
      using D.isAffine
  have hx : Point.map G.ι x ∈ Point.overOpen D.ambientCoordinateOpen := by
    simpa only [Point.overOpen, Set.mem_setOf_eq, LocalEtaleCoordinates.ambientCoordinateOpen,
      Scheme.Opens.ι_image_top] using D.mem
  change Function.Surjective
    (conormalPointDerivativeMap G.ι (G.k + G.k) x D.ambientCoordinateOpen hU hx)
  letI := overSpecAlgebra G.W D.ambientCoordinateOpen
  exact conormalPointDerivativeMap_surjective G.k (G.k + G.k) G.ι x D.ambientCoordinateOpen hU hx
    (chosenChartCoordinateMap G.W (G.k + G.k) (Point.map G.ι x))
    (chosenChartCoordinateMap_etale G.W (G.k + G.k) (Point.map G.ι x))
    (localChart G.W (G.k + G.k) (Point.map G.ι x) (Point.map G.ι x))
    (fun t => s2e_actual_coordinateSection_nativeAnalytic G.W (G.k + G.k) (Point.map G.ι x) hx t)

#print axioms canonicalConormalDerivative_surjective
#print axioms canonicalConormalDerivative
end HodgeLean.Foundations.Program.G32Native
