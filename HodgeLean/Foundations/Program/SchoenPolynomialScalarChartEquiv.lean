import HodgeLean.Foundations.Program.SchoenPolynomialScalarCharts
import HodgeLean.Foundations.Program.SchoenPolynomialScalarChartNaturality

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open MvPolynomial HomogeneousLocalization
open scoped TensorProduct
namespace HodgeLean.Foundations.Program

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual scalar-extension chart map reverses the constructed normalized chart inverse. -/
theorem s2_polynomialScalarChartMap_inverse (R ι : Type) [CommRing R] (i : ι)
    (z : Away (homogeneousSubmodule ι R) (s2_polynomialIntegralCoordinates R ι (X i))) :
    b54_relativeChartMap (s2_polynomialIntegralCoordinates R ι) (X i)
      (s2_polynomialScalarChartInverse R ι i z) = z := by
  let f := s2_polynomialIntegralCoordinates R ι
  let hf := f.map_mem (isHomogeneous_X (ULift.{0} ℤ) i)
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective (homogeneousSubmodule ι R) hf z
  change b54_relativeChartMap f (X i)
    (s2_normalizedChartLift (homogeneousSubmodule ι R) (f (X i))
      (s2_polynomialScalarChartEvaluation R ι i) _ (Away.mk _ hf n a ha)) = _
  rw [s2_normalizedChartLift_mk]
  have h := RingHom.congr_fun (s2_polynomialScalarChartMap_evaluation R ι i) a
  change b54_relativeChartMap f (X i) (s2_polynomialScalarChartEvaluation R ι i a) =
    b54_awayNormalize (homogeneousSubmodule ι R) hf a at h
  rw [h]
  exact b54_awayNormalize_homogeneous (homogeneousSubmodule ι R) hf n a
    (by simpa only [smul_eq_mul, Nat.mul_one] using ha)

/-- The constructed chart inverse takes original coefficient fractions to the actual left tensor factor. -/
theorem s2_polynomialScalarChartInverse_fromZero (R ι : Type) [CommRing R] (i : ι)
    (c : homogeneousSubmodule ι R 0) :
    s2_polynomialScalarChartInverse R ι i
      (fromZeroRingHom (homogeneousSubmodule ι R)
        (Submonoid.powers (s2_polynomialIntegralCoordinates R ι (X i))) c) = c ⊗ₜ[ℤ] 1 := by
  let f := s2_polynomialIntegralCoordinates R ι
  let hf := f.map_mem (isHomogeneous_X (ULift.{0} ℤ) i)
  change s2_normalizedChartLift (homogeneousSubmodule ι R) (f (X i))
    (s2_polynomialScalarChartEvaluation R ι i) _
    (Away.mk _ hf 0 c.val (by simpa only [zero_smul] using c.property)) = _
  rw [s2_normalizedChartLift_mk]
  exact s2_polynomialScalarChartEvaluation_zero R ι i c

/-- The constructed chart inverse takes mapped integer fractions to the actual right tensor factor. -/
theorem s2_polynomialScalarChartInverse_map (R ι : Type) [CommRing R] (i : ι)
    (b : Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)) :
    s2_polynomialScalarChartInverse R ι i
      (Away.map (s2_polynomialIntegralCoordinates R ι) (X i) b) = 1 ⊗ₜ[ℤ] b := by
  let f := s2_polynomialIntegralCoordinates R ι
  let hf := f.map_mem (isHomogeneous_X (ULift.{0} ℤ) i)
  obtain ⟨n, a, ha, rfl⟩ := Away.mk_surjective
    (homogeneousSubmodule ι (ULift.{0} ℤ)) (isHomogeneous_X _ i) b
  rw [Away.map_mk f (X i) (isHomogeneous_X _ i) n a ha]
  change s2_normalizedChartLift (homogeneousSubmodule ι R) (f (X i))
    (s2_polynomialScalarChartEvaluation R ι i) _
    (Away.mk _ hf n (f a) (f.map_mem ha)) = _
  rw [s2_normalizedChartLift_mk]
  have h := RingHom.congr_fun (s2_polynomialScalarChartEvaluation_integral R ι i) a
  change s2_polynomialScalarChartEvaluation R ι i (f a) =
    1 ⊗ₜ[ℤ] b54_awayNormalize (homogeneousSubmodule ι (ULift.{0} ℤ))
      (isHomogeneous_X _ i) a at h
  rw [h, b54_awayNormalize_homogeneous (homogeneousSubmodule ι (ULift.{0} ℤ))
    (isHomogeneous_X _ i) n a (by simpa only [smul_eq_mul, Nat.mul_one] using ha)]

/-- The constructed normalized inverse reverses the actual scalar-extension chart map. -/
theorem s2_polynomialScalarChartInverse_mapChart (R ι : Type) [CommRing R] (i : ι)
    (z : (homogeneousSubmodule ι R 0) ⊗[ℤ]
      Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)) :
    s2_polynomialScalarChartInverse R ι i
      (b54_relativeChartMap (s2_polynomialIntegralCoordinates R ι) (X i) z) = z := by
  let f := s2_polynomialIntegralCoordinates R ι
  let J := s2_polynomialScalarChartInverse R ι i
  let F := b54_relativeChartMap f (X i)
  have hleft (c : homogeneousSubmodule ι R 0) : J (F (c ⊗ₜ[ℤ] 1)) = c ⊗ₜ[ℤ] 1 := by
    change J (fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (f (X i))) c *
      Away.map f (X i) 1) = _
    rw [map_one, mul_one]
    exact s2_polynomialScalarChartInverse_fromZero R ι i c
  have hright (b : Away (homogeneousSubmodule ι (ULift.{0} ℤ)) (X i)) :
      J (F (1 ⊗ₜ[ℤ] b)) = 1 ⊗ₜ[ℤ] b := by
    change J (fromZeroRingHom (homogeneousSubmodule ι R) (Submonoid.powers (f (X i))) 1 *
      Away.map f (X i) b) = _
    rw [map_one, one_mul]
    exact s2_polynomialScalarChartInverse_map R ι i b
  change J (F z) = z
  induction z using TensorProduct.induction_on with
  | zero => rw [map_zero, map_zero]
  | tmul c b =>
    have heq : c ⊗ₜ[ℤ] b = (c ⊗ₜ[ℤ] 1) * (1 ⊗ₜ[ℤ] b) := by
      rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
    rw [heq, map_mul, map_mul, hleft, hright]
  | add x y hx hy => rw [map_add, map_add, hx, hy]

end HodgeLean.Foundations.Program
