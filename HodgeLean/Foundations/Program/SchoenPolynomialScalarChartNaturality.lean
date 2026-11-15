import HodgeLean.Foundations.Program.SchoenPolynomialScalarCharts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Normalized scalar-extension evaluation agrees with the actual right tensor factor on integer coordinates. -/
theorem s2_polynomialScalarChartEvaluation_integral (R ι : Type) [CommRing R] (i : ι) :
    (s2_polynomialScalarChartEvaluation R ι i).comp
      (s2_polynomialIntegralCoordinates R ι).toRingHom =
    (Algebra.TensorProduct.includeRight :
      Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i) →ₐ[ℤ]
        (homogeneousSubmodule ι R 0) ⊗[ℤ]
          Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)).toRingHom.comp
      (b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ)) (isHomogeneous_X _ i)) := by
  let F := (s2_polynomialScalarChartEvaluation R ι i).comp
    (s2_polynomialIntegralCoordinates R ι).toRingHom
  let H := (Algebra.TensorProduct.includeRight :
    Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i) →ₐ[ℤ]
      (homogeneousSubmodule ι R 0) ⊗[ℤ]
        Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)).toRingHom.comp
    (b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ)) (isHomogeneous_X _ i))
  change F = H
  apply MvPolynomial.ringHom_ext
  · intro r
    have h : (F.comp C).comp (ULift.ringEquiv.symm : ℤ ≃+* ULift.{0} ℤ).toRingHom =
        (H.comp C).comp (ULift.ringEquiv.symm : ℤ ≃+* ULift.{0} ℤ).toRingHom :=
      Subsingleton.elim _ _
    exact RingHom.congr_fun h r.down
  · intro j
    change s2_polynomialScalarChartEvaluation R ι i (s2_polynomialIntegralCoordinates R ι (X j)) = _
    rw [s2_polynomialIntegralCoordinates_X R ι j]
    change s2_polynomialScalarChartEvaluation R ι i (X j) =
      1 ⊗ₜ[ℤ] b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ))
        (isHomogeneous_X _ i) (X j)
    simp only [s2_polynomialScalarChartEvaluation, eval₂Hom_X']

end HodgeLean.Foundations.Program
