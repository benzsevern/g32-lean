import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveCharts
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.KrullDimension.Field

noncomputable section
set_option maxHeartbeats 400000
open AlgebraicGeometry AlgebraicGeometry.ComplexProjectiveSpace
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Polynomial coordinates on a projective affine chart after changing the coefficient ring.
Source: Hartshorne, Algebraic Geometry, II.2.5; Mathlib MvPolynomial.algebraTensorAlgEquiv. -/
def s0_projective_chart_baseChange_equiv
    (R : Type*) [CommRing R] [Algebra (ULift.{0} ℤ) R] {n : ℕ} (i : Fin (n + 1)) :
    letI : Algebra (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
    (s0_projective_chart_base i).toAlgebra
    letI : Module (ULift.{0} ℤ) R := Algebra.toModule
    letI : Module (ULift.{0} ℤ)
        (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
    R ⊗[ULift.{0} ℤ] HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i) ≃ₐ[R]
      MvPolynomial {j : Fin (n + 1) // j ≠ i} R :=
  letI : Algebra (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
    (s0_projective_chart_base i).toAlgebra
  letI : Module (ULift.{0} ℤ) R := Algebra.toModule
  letI : Module (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) (s0_projective_chart_algEquiv i).symm).trans
    (MvPolynomial.algebraTensorAlgEquiv (ULift.{0} ℤ) R)

#print axioms s0_projective_chart_baseChange_equiv

theorem s0_projective_chart_baseChange_domain
    (R : Type*) [CommRing R] [IsDomain R] [Algebra (ULift.{0} ℤ) R]
    {n : ℕ} (i : Fin (n + 1)) :
    letI : Algebra (ULift.{0} ℤ)
        (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
      (s0_projective_chart_base i).toAlgebra
    letI : Module (ULift.{0} ℤ) R := Algebra.toModule
    letI : Module (ULift.{0} ℤ)
        (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
    IsDomain (R ⊗[ULift.{0} ℤ]
      HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := by
  letI : Algebra (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
    (s0_projective_chart_base i).toAlgebra
  letI : Module (ULift.{0} ℤ) R := Algebra.toModule
  letI : Module (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
  exact (s0_projective_chart_baseChange_equiv R i).toRingEquiv.toMulEquiv.isDomain

#print axioms s0_projective_chart_baseChange_domain

theorem s0_projective_chart_baseChange_dimension
    (R : Type*) [Field R] [Algebra (ULift.{0} ℤ) R] {n : ℕ} (i : Fin (n + 1)) :
    letI : Algebra (ULift.{0} ℤ)
        (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
      (s0_projective_chart_base i).toAlgebra
    letI : Module (ULift.{0} ℤ) R := Algebra.toModule
    letI : Module (ULift.{0} ℤ)
        (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
    ringKrullDim (R ⊗[ULift.{0} ℤ]
      HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) = (n : WithBot ℕ∞) := by
  letI : Algebra (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
    (s0_projective_chart_base i).toAlgebra
  letI : Module (ULift.{0} ℤ) R := Algebra.toModule
  letI : Module (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
  have hc : Nat.card {j : Fin (n + 1) // j ≠ i} = n := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  rw [ringKrullDim_eq_of_ringEquiv (s0_projective_chart_baseChange_equiv R i).toRingEquiv,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, hc]

#print axioms s0_projective_chart_baseChange_dimension

end HodgeLean.Foundations.Program
