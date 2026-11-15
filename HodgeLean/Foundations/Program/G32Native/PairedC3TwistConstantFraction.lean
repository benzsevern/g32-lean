import HodgeLean.Foundations.Program.G32Native.PairedC3TwistConstantMonomial
import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateTwistingSection

/-! # The degree-zero constant monomial on the actual coordinate charts -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Cohomology.Cech.Proofs
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech Scheme.Modules
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native
variable (R : Type) [CommRing R] (n : ℕ)

/-- The constant polynomial monomial as an actual degree-zero fraction. -/
def pairedC3TwistConstantFraction (I : Finset (Fin (n + 1))) :
    GradedModule.Frac (GradedModule.FD R n 0) I :=
  GradedModule.twistFrac 0
    (Twist.Mon.incl n 0 (Finset.empty_subset I) (pairedC3TwistConstantMonomial n))

/-- The actual constant fraction has no denominator exponents. -/
theorem paired_c3_constant_fraction_denExp (I : Finset (Fin (n + 1)))
    (l : Fin (n + 1)) : (pairedC3TwistConstantFraction R n I).denExp l = 0 := rfl

/-- The actual numerator of the constant monomial is one. -/
theorem paired_c3_constant_fraction_num (I : Finset (Fin (n + 1))) :
    (pairedC3TwistConstantFraction R n I).num = (1 : MvPolynomial (Fin (n + 1)) R) := by
  change (∏ l : Fin (n + 1), (MvPolynomial.X l : MvPolynomial (Fin (n + 1)) R) ^
    (0 : ℤ).toNat) = 1
  simp only [Int.toNat_zero, pow_zero, Finset.prod_const_one]

/-- Trivializing degree zero does not add a denominator. -/
theorem paired_c3_constant_fraction_shift_denominator (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) :
    (∏ l : Fin (n + 1), (MvPolynomial.X l : MvPolynomial (Fin (n + 1)) R) ^
      (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 0 i hi
        (pairedC3TwistConstantFraction R n I)).denExp l) = 1 := by
  have hden (l : Fin (n + 1)) :
      (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 0 i hi
        (pairedC3TwistConstantFraction R n I)).denExp l = 0 := by
    change (pairedC3TwistConstantFraction R n I).denExp l + Pi.single (M := fun _ : Fin (n + 1) => ℕ) i 0 l = 0
    rw [paired_c3_constant_fraction_denExp]
    simp only [Pi.single_apply, ite_self, zero_add]
  simp only [hden, pow_zero, Finset.prod_const_one]

/-- The degree-zero chart coefficient is the original unit section. -/
theorem paired_c3_constant_fraction_coefficient (I : Finset (Fin (n + 1)))
    (i : Fin (n + 1)) (hi : i ∈ I) :
    (show Γ(Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R),
      ProjSpace.coordinateIntersection R n I) from
      ProjSpace.twistingFractionCoefficientEquiv R n 0 i hi
        (GradedModule.sec.mk _ I (pairedC3TwistConstantFraction R n I))) = 1 := by
  apply Subtype.ext
  funext x
  have : x.val.asHomogeneousIdeal.toIdeal.IsPrime :=
    (show ProjectiveSpectrum (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)
      from x.val).isPrime
  apply HomogeneousLocalization.val_injective
  rw [ProjSpace.twistingFractionCoefficientEquiv_apply,
    GradedModule.coordinateShiftEquiv_apply_mk]
  have he := ProjSpace.unitFreeFractionEquiv_apply_mk_val R n I ⟨i, hi⟩
    (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 0 i hi
      (pairedC3TwistConstantFraction R n I)) x
  erw [Proj.one_apply, HomogeneousLocalization.val_one]
  have hnum : (GradedModule.coordinateDenominatorFrac (GradedModule.free R n) 0 i hi
      (pairedC3TwistConstantFraction R n I)).num =
        (1 : MvPolynomial (Fin (n + 1)) R) := paired_c3_constant_fraction_num R n I
  simp only [paired_c3_constant_fraction_shift_denominator, hnum] at he
  change _ = Localization.mk (1 : MvPolynomial (Fin (n + 1)) R)
    (1 : x.val.asHomogeneousIdeal.toIdeal.primeCompl) at he
  rw [Localization.mk_one_eq_algebraMap, map_one] at he
  exact he

end HodgeLean.Foundations.Program.G32Native
