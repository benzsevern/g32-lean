import HodgeLean.Foundations.Program.SchoenPolynomialScalarChartIso
import HodgeLean.Foundations.Program.SchoenCycleProjectiveCharts
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.Basic

/-! # Polynomial coordinates on the original complex homogeneous affine charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry MvPolynomial HomogeneousLocalization
open scoped TensorProduct
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- Transport of an actual homogeneous fraction along an equality of
its denominators leaves its numerator and exponent unchanged. -/
theorem paired_c3_away_cast_mk {A σ : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G]
    {x y : A} (h : x = y) {d : ℕ} (hx : x ∈ G d)
    (n : ℕ) (a : A) (ha : a ∈ G (n • d)) :
    RingEquiv.cast (R := fun z => Away G z) h (Away.mk G hx n a ha) =
      Away.mk G (h ▸ hx) n a ha := by
  cases h
  rfl

/-- Forward and backward transport of a homogeneous localization cancel. -/
theorem paired_c3_away_cast_cancel {A σ : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G]
    {x y : A} (h : x = y) (z : Away G x) :
    RingEquiv.cast (R := fun z => Away G z) h.symm
      (RingEquiv.cast (R := fun z => Away G z) h z) = z := by
  cases h
  rfl

/-- Denominator transport preserves each degree-zero coefficient. -/
theorem paired_c3_away_cast_fromZero {A σ : Type} [CommRing A]
    [SetLike σ A] [AddSubgroupClass σ A] (G : ℕ → σ) [GradedRing G]
    {x y : A} (h : x = y) (c : G 0) :
    RingEquiv.cast (R := fun z => Away G z) h
      (fromZeroRingHom G (.powers x) c) = fromZeroRingHom G (.powers y) c := by
  cases h
  rfl

/-- Polynomial coordinates before transporting the scalar-extension
denominator back to its literal homogeneous variable. -/
def pairedC3PolynomialScalarChartCoordinates (k : ℕ) (i : Fin (k + 1)) :
    Away (homogeneousSubmodule (Fin (k + 1)) ℂ)
      ((s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))) (X i)) ≃+*
      MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ := by
  let f := s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))
  let eMap := RingEquiv.ofBijective (b54_relativeChartMap f (X i)).toRingHom
    (s2_polynomialScalarChartMap_bijective ℂ (Fin (k + 1)) i)
  let eCoeff := Algebra.TensorProduct.congr
    (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).toIntAlgEquiv
    (AlgEquiv.refl : Away (ComplexProjectiveSpace.UniversalGrading k) (X i) ≃ₐ[ℤ]
      Away (ComplexProjectiveSpace.UniversalGrading k) (X i))
  exact
    eMap.symm.trans (eCoeff.toRingEquiv.trans (s2e_complexChartRingEquiv i).toRingEquiv)

/-- Identify the actual complex degree-zero localization with the
polynomial ring on the non-denominator homogeneous coordinates. -/
def pairedC3PolynomialChartCoordinates (k : ℕ) (i : Fin (k + 1)) :
    Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) ≃+*
      MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ :=
  (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
    (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i).symm).trans
      (pairedC3PolynomialScalarChartCoordinates k i)

/-- The inverse scalar-extension map on original integer fractions
retains their original normalized polynomial coordinates. -/
theorem paired_c3_polynomial_scalar_chart_coordinates_integral
    (k : ℕ) (i : Fin (k + 1))
    (z : Away (ComplexProjectiveSpace.UniversalGrading k) (X i)) :
    pairedC3PolynomialScalarChartCoordinates k i
      (Away.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))) (X i) z) =
      s2e_complexChartRingEquiv i (1 ⊗ₜ[ℤ] z) := by
  let f := s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))
  let eMap := RingEquiv.ofBijective (b54_relativeChartMap f (X i)).toRingHom
    (s2_polynomialScalarChartMap_bijective ℂ (Fin (k + 1)) i)
  have hi (a) : eMap.symm a = s2_polynomialScalarChartInverse ℂ (Fin (k + 1)) i a := by
    apply eMap.injective
    rw [RingEquiv.apply_symm_apply]
    exact (s2_polynomialScalarChartMap_inverse ℂ (Fin (k + 1)) i a).symm
  change s2e_complexChartRingEquiv i
    ((Algebra.TensorProduct.congr
      (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).toIntAlgEquiv
      (AlgEquiv.refl : Away (ComplexProjectiveSpace.UniversalGrading k) (X i) ≃ₐ[ℤ] _))
        (eMap.symm (Away.map f (X i) z))) = _
  rw [hi, s2_polynomialScalarChartInverse_map]
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
    map_one]
  rfl

/-- Original integral ratios retain their numerator index after scalar extension. -/
theorem paired_c3_polynomial_scalar_chart_coordinates_ratio
    (k : ℕ) (i j : Fin (k + 1)) :
    pairedC3PolynomialScalarChartCoordinates k i
      (Away.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))) (X i)
        (ComplexProjectiveSpace.chartCoordinate i j)) =
      if h : j = i then 1 else X ⟨j, h⟩ :=
  (paired_c3_polynomial_scalar_chart_coordinates_integral k i _).trans
    (s2e_complexChartRingEquiv_coordinate i j)

/-- Scalar extension followed by denominator transport gives the original
complex homogeneous ratio, including its numerator and denominator. -/
theorem paired_c3_scalar_extension_ratio (k : ℕ) (i j : Fin (k + 1)) :
    RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
      (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i)
      (Away.map (s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))) (X i)
        (ComplexProjectiveSpace.chartCoordinate i j)) = ProjSpace.ratio ℂ k i j := by
  unfold ComplexProjectiveSpace.chartCoordinate
  rw [Away.map_mk, paired_c3_away_cast_mk]
  apply HomogeneousLocalization.val_injective
  simp only [Away.val_mk, ProjSpace.ratio, s2_polynomialIntegralCoordinates_X]

/-- The chart equivalence sends each actual homogeneous ratio to its
literal polynomial coordinate, with the denominator coordinate equal to one. -/
theorem paired_c3_polynomial_chart_coordinates_ratio (k : ℕ) (i j : Fin (k + 1)) :
    pairedC3PolynomialChartCoordinates k i (ProjSpace.ratio ℂ k i j) =
      if h : j = i then 1 else X ⟨j, h⟩ := by
  rw [← paired_c3_scalar_extension_ratio k i j]
  change pairedC3PolynomialScalarChartCoordinates k i
    (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
      (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i).symm
      (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z)
        (s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i) _)) = _
  rw [paired_c3_away_cast_cancel, paired_c3_polynomial_scalar_chart_coordinates_ratio]

/-- Actual degree-zero coefficients remain their original polynomial constants. -/
theorem paired_c3_polynomial_scalar_chart_coordinates_fromZero
    (k : ℕ) (i : Fin (k + 1)) (c : homogeneousSubmodule (Fin (k + 1)) ℂ 0) :
    pairedC3PolynomialScalarChartCoordinates k i
      (fromZeroRingHom (homogeneousSubmodule (Fin (k + 1)) ℂ)
        (.powers ((s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))) (X i))) c) =
      C ((ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ) c) := by
  let f := s2_polynomialIntegralCoordinates ℂ (Fin (k + 1))
  let eMap := RingEquiv.ofBijective (b54_relativeChartMap f (X i)).toRingHom
    (s2_polynomialScalarChartMap_bijective ℂ (Fin (k + 1)) i)
  have hc : eMap (c ⊗ₜ[ℤ] 1) =
      fromZeroRingHom (homogeneousSubmodule (Fin (k + 1)) ℂ) (.powers (f (X i))) c := by
    change fromZeroRingHom _ _ c * Away.map f (X i) 1 = _
    rw [map_one, mul_one]
  change s2e_complexChartRingEquiv i
    ((Algebra.TensorProduct.congr
      (ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ).toIntAlgEquiv
      (AlgEquiv.refl : Away (ComplexProjectiveSpace.UniversalGrading k) (X i) ≃ₐ[ℤ] _))
        (eMap.symm (fromZeroRingHom _ _ c))) = _
  rw [← hc, RingEquiv.symm_apply_apply]
  simp only [Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul, map_one]
  exact (s2e_complexChartRingEquiv i).commutes
    ((ProjectiveSpace.degreeZeroEquiv (Fin (k + 1)) ℂ) c)

/-- The normalized chart equivalence preserves the actual complex scalar action. -/
theorem paired_c3_polynomial_chart_coordinates_algebraMap
    (k : ℕ) (i : Fin (k + 1)) (c : ℂ) :
    pairedC3PolynomialChartCoordinates k i
      (algebraMap ℂ (Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)) c) = C c := by
  let h := s2_polynomialIntegralCoordinates_X ℂ (Fin (k + 1)) i
  have hc := paired_c3_away_cast_fromZero (homogeneousSubmodule (Fin (k + 1)) ℂ) h
    (ProjSpace.grad0Equiv ℂ k c)
  change RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z) h
      (fromZeroRingHom _ _ (ProjSpace.grad0Equiv ℂ k c)) =
    algebraMap ℂ (Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i)) c at hc
  rw [← hc]
  change pairedC3PolynomialScalarChartCoordinates k i
    (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z) h.symm
      (RingEquiv.cast (R := fun z => Away (homogeneousSubmodule (Fin (k + 1)) ℂ) z) h _)) = _
  rw [paired_c3_away_cast_cancel, paired_c3_polynomial_scalar_chart_coordinates_fromZero]
  congr 1
  change (MvPolynomial.C c).coeff 0 = c
  exact MvPolynomial.coeff_zero_C c

/-- The same chart coordinates as an equivalence of complex algebras. -/
def pairedC3PolynomialChartAlgEquiv (k : ℕ) (i : Fin (k + 1)) :
    Away (homogeneousSubmodule (Fin (k + 1)) ℂ) (X i) ≃ₐ[ℂ]
      MvPolynomial {j : Fin (k + 1) // j ≠ i} ℂ where
  __ := pairedC3PolynomialChartCoordinates k i
  commutes' c := paired_c3_polynomial_chart_coordinates_algebraMap k i c

/-- A polynomial chart variable is the corresponding original ratio,
with coefficient one, under the inverse chart map. -/
theorem paired_c3_polynomial_chart_inverse_variable (k : ℕ) (i : Fin (k + 1))
    (j : {j : Fin (k + 1) // j ≠ i}) :
    (pairedC3PolynomialChartAlgEquiv k i).symm (X j) = ProjSpace.ratio ℂ k i j.val := by
  have h : pairedC3PolynomialChartAlgEquiv k i (ProjSpace.ratio ℂ k i j.val) = X j := by
    change pairedC3PolynomialChartCoordinates k i (ProjSpace.ratio ℂ k i j.val) = X j
    rw [paired_c3_polynomial_chart_coordinates_ratio, dite_eq_right j.property]
  rw [← h, AlgEquiv.symm_apply_apply]

end HodgeLean.Foundations.Program.G32Native
