import HodgeLean.Foundations.Program.G32Native.PairedC3TwistConstantFraction
import HodgeLean.Foundations.Program.G32Native.PairedConormalGlobalSectionCoordinates

/-! # Actual constant sections from degree-zero twisting cocycles -/
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

/-- The constant fraction represents the actual unit section in degree zero. -/
theorem paired_c3_constant_fraction_sectionAt
    (I : Finset (Fin (n + 1))) (i : Fin (n + 1)) (hi : i ∈ I) :
    ProjSpace.twistingFractionSectionEquivAt R n 0 i hi
      (GradedModule.sec.mk _ I (pairedC3TwistConstantFraction R n I)) =
      ((ProjSpace.twistingSheaf R n).tensorPow 0).presheaf.map
        (homOfLE (le_top : ProjSpace.coordinateIntersection R n I ≤ ⊤)).op
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n 0) 0) := by
  rw [ProjSpace.twistingFractionSectionEquivAt_apply, paired_c3_constant_fraction_coefficient]
  simp only [one_smul, tensorPowSection_zero]

/-- The degree-zero section comparison retains the constant on every intersection. -/
theorem paired_c3_constant_fraction_section (I : Finset (Fin (n + 1))) (hI : I.Nonempty) :
    ProjSpace.twistingFractionSectionEquiv R n 0 I hI
      (GradedModule.sec.mk _ I (pairedC3TwistConstantFraction R n I)) =
      ((ProjSpace.twistingSheaf R n).tensorPow 0).presheaf.map
        (homOfLE (le_top : ProjSpace.coordinateIntersection R n I ≤ ⊤)).op
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n 0) 0) :=
  paired_c3_constant_fraction_sectionAt R n I (I.min' hI) (Finset.min'_mem I hI)

/-- The constant monomial retains its original fraction on every vertex. -/
theorem paired_c3_constant_cochain_fraction (t : Idx n 0) :
    GradedModule.cochainTwistEquiv (R := R) (n := n) 0 0
      (Twist.constSec R 0 (Finsupp.single (pairedC3TwistConstantMonomial n) 1)) t =
      GradedModule.sec.mk _ (Idx.img n t)
        (pairedC3TwistConstantFraction R n (Idx.img n t)) := by
  change GradedModule.twistToGradSec 0 (Idx.img n t)
    (Finsupp.lmapDomain R R (Twist.Mon.incl n 0 (Finset.empty_subset _))
      (Finsupp.single (pairedC3TwistConstantMonomial n) 1)) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    GradedModule.twistToGradSec_single, one_smul]
  rfl

/-- The actual Cech comparison sends the constant monomial to the unit section. -/
theorem paired_c3_constant_cochain_actual :
    paired_twistCochainEquiv R n 0 0
      (Twist.constSec R 0 (Finsupp.single (pairedC3TwistConstantMonomial n) 1)) =
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf R n 0)
        (ProjSpace.stdCoverPullback (𝟙 (Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))))
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n 0) 0) := by
  funext s
  change ProjSpace.twistingCochainEquiv R n 0 0
    (GradedModule.cochainTwistEquiv (R := R) (n := n) 0 0
      (Twist.constSec R 0 (Finsupp.single (pairedC3TwistConstantMonomial n) 1))) s = _
  rw [ProjSpace.twistingCochainEquiv_apply, paired_c3_constant_cochain_fraction]
  erw [paired_c3_constant_fraction_section]
  exact (ProjSpace.twistingSectionPresheaf R n 0).res_res _ _ _

/-- The Cech comparison retains the original coefficient of a constant. -/
theorem paired_c3_constant_cochain_scalar (r : R) :
    paired_twistCochainEquiv R n 0 0
      (Twist.constSec R 0 (Finsupp.single (pairedC3TwistConstantMonomial n) r)) =
      r • pairedCechRestriction (ProjSpace.twistingSectionPresheaf R n 0)
        (ProjSpace.stdCoverPullback (𝟙 (Proj
          (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))))
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n 0) 0) := by
  have hg : (Finsupp.single (pairedC3TwistConstantMonomial n) r : Twist.Mon n 0 ∅ →₀ R) =
      r • Finsupp.single (pairedC3TwistConstantMonomial n) 1 := by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hg, LinearMap.map_smul, LinearEquiv.map_smul, paired_c3_constant_cochain_actual]

/-- Actual global sections of the structure module are constants.
Source: Hartshorne, Algebraic Geometry, III.5.1, degree-zero computation. -/
theorem paired_c3_global_unit_section_span (hn : 1 ≤ n)
    (s : (ProjSpace.twistingSectionPresheaf R n 0).obj ⊤) :
    ∃ r : R, s = r • (show (ProjSpace.twistingSectionPresheaf R n 0).obj ⊤ from
      tensorPowSection (ProjSpace.twistingCoordinateSection R n 0) 0) := by
  let F := ProjSpace.twistingSectionPresheaf R n 0
  let K := ProjSpace.stdCoverPullback (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))
  obtain ⟨r, hr⟩ := paired_c3_twisting_zero_cocycle_constant R n hn
    (pairedCechRestriction F K s) (pairedCechRestriction_cocycle F K s)
  rw [paired_c3_constant_cochain_scalar] at hr
  refine ⟨r, ?_⟩
  apply pairedCechRestriction_injective ((𝟙 _) ≫ ProjSpace.π R n)
    ((ProjSpace.twistingSheaf R n).tensorPow 0) K
  funext i
  have hi := congrFun hr i
  simpa only [pairedCechRestriction, LinearMap.map_smul, Pi.smul_apply] using hi.symm

end HodgeLean.Foundations.Program.G32Native
