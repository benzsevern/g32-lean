import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveBaseChange
import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveSmooth

noncomputable section
set_option maxRecDepth 2000
set_option maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.ComplexProjectiveSpace
open scoped TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] MvPolynomial.gradedAlgebra

/-- A projective affine chart after base change is the spectrum of a polynomial ring.
Source: Hartshorne, Algebraic Geometry, II.2.5 and II.3.3, affine charts and affine fibre products. -/
def s0_projective_chart_fiber_iso
    (R : Type) [CommRing R] [Algebra (ULift.{0} ℤ) R] {n : ℕ} (i : Fin (n + 1)) :
    pullback (terminal.from (Spec ↧R))
      (terminal.from (Spec ↧(HomogeneousLocalization.Away
        (UniversalGrading.{0} n) (MvPolynomial.X i)))) ≅
      Spec ↧(MvPolynomial {j : Fin (n + 1) // j ≠ i} R) := by
  letI : Algebra (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) :=
    (s0_projective_chart_base i).toAlgebra
  letI : Module (ULift.{0} ℤ) R := Algebra.toModule
  letI : Module (ULift.{0} ℤ)
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) := Algebra.toModule
  let e := terminalIsTerminal.uniqueUpToIso
    (specULiftZIsTerminal : IsTerminal (Spec ↧(ULift.{0} ℤ)))
  exact (asIso (pullback.map _ _ _ _ (𝟙 _) (𝟙 _) e.hom
    (specULiftZIsTerminal.hom_ext _ _) (specULiftZIsTerminal.hom_ext _ _))) ≪≫
    pullbackSpecIso (ULift.{0} ℤ) R
      (HomogeneousLocalization.Away (UniversalGrading.{0} n) (MvPolynomial.X i)) ≪≫
    Scheme.Spec.mapIso (s0_projective_chart_baseChange_equiv R i).toRingEquiv.symm.toCommRingCatIso.op

#print axioms s0_projective_chart_fiber_iso

theorem s0_projective_chart_fiber_integral
    (R : Type) [CommRing R] [IsDomain R] [Algebra (ULift.{0} ℤ) R]
    {n : ℕ} (i : Fin (n + 1)) :
    IsIntegral (pullback (terminal.from (Spec ↧R))
      (terminal.from (Spec ↧(HomogeneousLocalization.Away
        (UniversalGrading.{0} n) (MvPolynomial.X i))))) := by
  exact IsIntegral.of_isIso (s0_projective_chart_fiber_iso R i).inv

#print axioms s0_projective_chart_fiber_integral

set_option backward.isDefEq.respectTransparency.types false in
theorem s0_projective_chart_fiber_dimension
    (R : Type) [Field R] [Algebra (ULift.{0} ℤ) R] {n : ℕ} (i : Fin (n + 1)) :
    letI := s0_projective_chart_fiber_integral R i
    TopologicalSpace.dim (pullback (terminal.from (Spec ↧R))
      (terminal.from (Spec ↧(HomogeneousLocalization.Away
        (UniversalGrading.{0} n) (MvPolynomial.X i)))) : Scheme.{0}) = n := by
  letI := s0_projective_chart_fiber_integral R i
  have hc : Nat.card {j : Fin (n + 1) // j ≠ i} = n := by
    simp [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
  unfold TopologicalSpace.dim
  rw [IsHomeomorph.topologicalKrullDim_eq _ (s0_projective_chart_fiber_iso R i).hom.homeomorph.isHomeomorph]
  change ((topologicalKrullDim (PrimeSpectrum (MvPolynomial {j : Fin (n + 1) // j ≠ i} R))).unbotD 0).toNat = n
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim,
    MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite,
    ringKrullDim_eq_zero_of_field, zero_add, hc]
  simp

#print axioms s0_projective_chart_fiber_dimension

end HodgeLean.Foundations.Program
