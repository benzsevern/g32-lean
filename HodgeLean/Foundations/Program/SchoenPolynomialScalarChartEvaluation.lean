import HodgeLean.Foundations.Program.SchoenNormalizedChartLift
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Normalize
import HodgeLean.Foundations.Program.TorusAlgebraizationB54Projective

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial evaluation in the actual scalar-extension chart, with its selected coordinate normalized. -/
def s2_polynomialScalarChartEvaluation (R ι : Type) [CommRing R] (i : ι) :
    MvPolynomial ι R →+*
      (homogeneousSubmodule ι R 0) ⊗[ℤ]
        Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i) :=
  eval₂Hom
    ((Algebra.TensorProduct.includeLeft :
      (homogeneousSubmodule ι R 0) →ₐ[ℤ]
        (homogeneousSubmodule ι R 0) ⊗[ℤ]
          Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)).toRingHom.comp
            (ProjectiveSpace.degreeZeroEquiv ι R).symm.toRingHom)
    (fun j => 1 ⊗ₜ[ℤ] b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ))
      (isHomogeneous_X _ i) (X j))

/-- The selected polynomial coordinate evaluates to one in the actual scalar-extension chart. -/
theorem s2_polynomialScalarChartEvaluation_self (R ι : Type) [CommRing R] (i : ι) :
    s2_polynomialScalarChartEvaluation R ι i (X i) = 1 := by
  simp only [s2_polynomialScalarChartEvaluation, eval₂Hom_X']
  rw [b54_awayNormalize_self (homogeneousSubmodule ι (ULift.{0} ℤ)) (isHomogeneous_X _ i)]
  rfl

/-- Normalized polynomial evaluation retains every actual degree-zero coefficient in the left tensor factor. -/
theorem s2_polynomialScalarChartEvaluation_zero (R ι : Type) [CommRing R] (i : ι)
    (c : homogeneousSubmodule ι R 0) :
    s2_polynomialScalarChartEvaluation R ι i c.val = c ⊗ₜ[ℤ] 1 := by
  have hc : C ((ProjectiveSpace.degreeZeroEquiv ι R) c) = c.val :=
    congrArg Subtype.val ((ProjectiveSpace.degreeZeroEquiv ι R).symm_apply_apply c)
  rw [← hc]
  simp only [s2_polynomialScalarChartEvaluation, eval₂Hom_C, RingHom.comp_apply]
  exact congrArg (fun a : homogeneousSubmodule ι R 0 => a ⊗ₜ[ℤ]
    (1 : Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)))
      ((ProjectiveSpace.degreeZeroEquiv ι R).symm_apply_apply c)

end HodgeLean.Foundations.Program
