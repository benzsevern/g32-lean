import HodgeLean.Foundations.Program.SchoenPolynomialScalarChartEquiv

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization CategoryTheory AlgebraicGeometry
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The polynomial scalar-extension chart map is bijective. -/
theorem s2_polynomialScalarChartMap_bijective (R ι : Type) [CommRing R] (i : ι) :
    Function.Bijective (b54_relativeChartMap (s2_polynomialIntegralCoordinates R ι) (X i)) := by
  exact ⟨Function.LeftInverse.injective (s2_polynomialScalarChartInverse_mapChart R ι i),
    Function.RightInverse.surjective (s2_polynomialScalarChartMap_inverse R ι i)⟩

end HodgeLean.Foundations.Program
