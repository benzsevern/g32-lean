import HodgeLean.Foundations.Program.SchoenPolynomialScalarChartEvaluation

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual integral polynomial coordinate map into a polynomial grading over the coefficient ring. -/
def s2_polynomialIntegralCoordinates (R ι : Type) [CommRing R] :
    homogeneousSubmodule ι (ULift.{0} ℤ) →+*ᵍ homogeneousSubmodule ι R :=
  b54_integralGradedCoordinates (homogeneousSubmodule ι R) (X : ι → MvPolynomial ι R)
    (isHomogeneous_X R)

/-- The actual integral polynomial coordinate map preserves each variable. -/
theorem s2_polynomialIntegralCoordinates_X (R ι : Type) [CommRing R] (i : ι) :
    s2_polynomialIntegralCoordinates R ι (X i) = (X i : MvPolynomial ι R) :=
  b54_integralGradedCoordinates_X _ _ _ i

/-- The actual normalized evaluation gives a reverse ring map for the polynomial scalar-extension chart. -/
def s2_polynomialScalarChartInverse (R ι : Type) [CommRing R] (i : ι) :
    Away (homogeneousSubmodule ι R) (s2_polynomialIntegralCoordinates R ι (X i)) →+*
      (homogeneousSubmodule ι R 0) ⊗[ℤ]
        Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i) :=
  s2_normalizedChartLift (homogeneousSubmodule ι R)
    (s2_polynomialIntegralCoordinates R ι (X i))
    (s2_polynomialScalarChartEvaluation R ι i) (by
      rw [s2_polynomialIntegralCoordinates_X, s2_polynomialScalarChartEvaluation_self])

/-- The actual scalar-extension chart map sends normalized polynomial evaluation to homogeneous normalization. -/
theorem s2_polynomialScalarChartMap_evaluation (R ι : Type) [CommRing R] (i : ι) :
    (b54_relativeChartMap (s2_polynomialIntegralCoordinates R ι) (X i)).toRingHom.comp
      (s2_polynomialScalarChartEvaluation R ι i) =
    b54_awayNormalize (homogeneousSubmodule ι R)
      ((s2_polynomialIntegralCoordinates R ι).map_mem (isHomogeneous_X _ i)) := by
  let f := s2_polynomialIntegralCoordinates R ι
  apply MvPolynomial.ringHom_ext
  · intro r
    have hC : s2_polynomialScalarChartEvaluation R ι i (C r) =
        ((ProjectiveSpace.degreeZeroEquiv ι R).symm r) ⊗ₜ[ℤ] 1 := by
      simp only [s2_polynomialScalarChartEvaluation, eval₂Hom_C, RingHom.comp_apply]
      rfl
    rw [RingHom.comp_apply, hC]
    change fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (f (X i)))
        ((ProjectiveSpace.degreeZeroEquiv ι R).symm r) * Away.map f (X i) 1 = _
    rw [map_one, mul_one]
    exact (b54_awayNormalize_fromZero (homogeneousSubmodule ι R)
      (f.map_mem (isHomogeneous_X _ i))
      ((ProjectiveSpace.degreeZeroEquiv ι R).symm r)).symm
  · intro j
    have hX : s2_polynomialScalarChartEvaluation R ι i (X j) =
        1 ⊗ₜ[ℤ] b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ))
          (isHomogeneous_X _ i) (X j) := by
      simp only [s2_polynomialScalarChartEvaluation, eval₂Hom_X']
    rw [RingHom.comp_apply, hX]
    change fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (f (X i))) 1 *
      Away.map f (X i) (b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ))
        (isHomogeneous_X _ i) (X j)) = _
    rw [map_one, one_mul, b54_awayNormalize_homogeneous
      (homogeneousSubmodule ι (ULift.{0} ℤ)) (isHomogeneous_X _ i) 1 (X j)
        (isHomogeneous_X _ j)]
    rw [Away.map_mk f (X i) (isHomogeneous_X _ i) 1 (X j)
      (by simpa using isHomogeneous_X (ULift.{0} ℤ) j)]
    rw [b54_awayNormalize_homogeneous (homogeneousSubmodule ι R)
      (f.map_mem (isHomogeneous_X _ i)) 1 (X j) (isHomogeneous_X _ j)]
    apply HomogeneousLocalization.val_injective
    simp only [Away.val_mk]
    change Localization.mk (s2_polynomialIntegralCoordinates R ι (X j)) _ =
      Localization.mk (X j) _
    exact congrArg (fun a : MvPolynomial ι R =>
      Localization.mk a (⟨f (X i) ^ 1, ⟨1, rfl⟩⟩ : Submonoid.powers (f (X i))))
        (s2_polynomialIntegralCoordinates_X R ι j)

end HodgeLean.Foundations.Program
