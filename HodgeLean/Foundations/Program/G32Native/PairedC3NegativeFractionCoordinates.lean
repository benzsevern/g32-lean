import HodgeLean.Foundations.Program.G32Native.PairedC3ShiftIdentities
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingFractionSections

/-! # Actual regular coefficients for degree minus one fractions -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program.G32Native
open ProjSpaceCech AlgebraicGeometry.ProjSpace
open AlgebraicCurves.Cohomology.Cech.Proofs
open OModulePresheaf_cechFinite_unit_of_isClosedImmersion_proj.AlgebraicGeometry.ProjSpace
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Equal graded modules have the same actual homogeneous fraction sections. -/
def pairedC3FractionEquivOfEq {R : Type} [CommRing R] {n : ℕ}
    {D E : GradedModule R n} (h : D = E) (I : Finset (Fin (n + 1))) :
    GradedModule.sec D I ≃ₗ[R] GradedModule.sec E I := by
  subst E
  exact LinearEquiv.refl _ _

/-- Multiplication by the inverted coordinate gives the local coefficient
of a degree minus one fraction in the dual coordinate frame. -/
def pairedC3NegativeFractionCoefficient (R : Type) [CommRing R] (n : ℕ)
    {I : Finset (Fin (n + 1))} (i : Fin (n + 1)) (hi : i ∈ I) :
    GradedModule.sec (GradedModule.FD R n (-1)) I ≃ₗ[R]
      (OModulePresheaf.unit ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) R))) ≫ π R n)).obj (coordinateIntersection R n I) := by
  have h : ((GradedModule.free R n).shift (-1)).shift 1 = GradedModule.free R n := by
    rw [paired_c3_shift_add]
    norm_num
    exact paired_c3_shift_zero _
  exact (GradedModule.coordinateShiftEquiv ((GradedModule.free R n).shift (-1)) 1 i hi).symm ≪≫ₗ
    pairedC3FractionEquivOfEq h I ≪≫ₗ unitFreeFractionEquiv R n I ⟨i, hi⟩

#print axioms pairedC3NegativeFractionCoefficient
/-- Transport along an equality of graded modules commutes with further
homogeneous localization. -/
theorem paired_c3_fraction_eq_restrict {R : Type} [CommRing R] {n : ℕ}
    {D E : GradedModule R n} (h : D = E)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J) (z : GradedModule.sec D I) :
    pairedC3FractionEquivOfEq h J (GradedModule.secIncl D hIJ z) =
      GradedModule.secIncl E hIJ (pairedC3FractionEquivOfEq h I z) := by
  subst E
  rfl

#print axioms paired_c3_fraction_eq_restrict
/-- The negative-fraction coefficient commutes with restriction to a
smaller coordinate intersection when the same frame coordinate is retained. -/
theorem paired_c3_negative_coefficient_restrict (R : Type) [CommRing R] (n : ℕ)
    {I J : Finset (Fin (n + 1))} (hIJ : I ⊆ J)
    (i : Fin (n + 1)) (hi : i ∈ I)
    (z : GradedModule.sec (GradedModule.FD R n (-1)) I) :
    pairedC3NegativeFractionCoefficient R n i (hIJ hi) (GradedModule.secIncl _ hIJ z) =
      (OModulePresheaf.unit ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule
        (Fin (n + 1)) R))) ≫ π R n)).res
        (coordinateIntersection_mono R n hIJ)
        (pairedC3NegativeFractionCoefficient R n i hi z) := by
  let D := (GradedModule.free R n).shift (-1)
  have h : D.shift 1 = GradedModule.free R n := by
    dsimp only [D]
    rw [paired_c3_shift_add]
    norm_num
    exact paired_c3_shift_zero _
  change unitFreeFractionEquiv R n J ⟨i, hIJ hi⟩
      (pairedC3FractionEquivOfEq h J
        ((GradedModule.coordinateRaiseHom D 1 i).secMap J (GradedModule.secIncl D hIJ z))) =
    (OModulePresheaf.unit ((𝟙 (Proj (MvPolynomial.homogeneousSubmodule
      (Fin (n + 1)) R))) ≫ π R n)).res _
      (unitFreeFractionEquiv R n I ⟨i, hi⟩
        (pairedC3FractionEquivOfEq h I ((GradedModule.coordinateRaiseHom D 1 i).secMap I z)))
  have hr := LinearMap.congr_fun
    ((GradedModule.coordinateRaiseHom D 1 i).secMap_incl hIJ) z
  change GradedModule.secIncl (D.shift 1) hIJ
      ((GradedModule.coordinateRaiseHom D 1 i).secMap I z) =
    (GradedModule.coordinateRaiseHom D 1 i).secMap J (GradedModule.secIncl D hIJ z) at hr
  calc
    _ = unitFreeFractionEquiv R n J ⟨i, hIJ hi⟩
        (pairedC3FractionEquivOfEq h J (GradedModule.secIncl (D.shift 1) hIJ
          ((GradedModule.coordinateRaiseHom D 1 i).secMap I z))) :=
      congrArg (fun t => unitFreeFractionEquiv R n J ⟨i, hIJ hi⟩
        (pairedC3FractionEquivOfEq h J t)) hr.symm
    _ = unitFreeFractionEquiv R n J ⟨i, hIJ hi⟩
        (GradedModule.secIncl (GradedModule.free R n) hIJ
          (pairedC3FractionEquivOfEq h I ((GradedModule.coordinateRaiseHom D 1 i).secMap I z))) :=
      congrArg (unitFreeFractionEquiv R n J ⟨i, hIJ hi⟩)
        (paired_c3_fraction_eq_restrict h hIJ _)
    _ = _ := unitFreeFractionEquiv_restrict R n hIJ ⟨i, hi⟩ _

#print axioms paired_c3_negative_coefficient_restrict
end HodgeLean.Foundations.Program.G32Native
