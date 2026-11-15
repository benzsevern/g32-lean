import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateTwistingSection
import HodgeLean.Foundations.Program.G32Native.PairedConormalCechSections

/-! # The original coordinate monomials give the actual coordinate section cocycles -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The original coordinate zero cocycle is the monomial with coefficient one. -/
def paired_twist_coordinateCochain (R : Type) [CommRing R] (n : ℕ)
    (j : Fin (n + 1)) : Twist.cochain R n 1 0 :=
  Twist.constSec R 1 (Finsupp.single (paired_twist_coordinateMonomial n j) 1)

/-- On each original simplex the monomial map retains the actual coordinate fraction. -/
theorem paired_twist_coordinateCochain_fraction
    (R : Type) [CommRing R] (n : ℕ) (j : Fin (n + 1)) (t : Idx n 0) :
    GradedModule.cochainTwistEquiv (R := R) (n := n) 1 0
      (paired_twist_coordinateCochain R n j) t =
      GradedModule.sec.mk _ (Idx.img n t)
        (paired_twist_coordinateFraction R n (Idx.img n t) j) := by
  change GradedModule.twistToGradSec 1 (Idx.img n t)
    (Finsupp.lmapDomain R R (Twist.Mon.incl n 1 (Finset.empty_subset _))
      (Finsupp.single (paired_twist_coordinateMonomial n j) 1)) = _
  rw [Finsupp.lmapDomain_apply, Finsupp.mapDomain_single,
    GradedModule.twistToGradSec_single, one_smul]
  rfl

/-- The actual Cech comparison sends each original coordinate monomial to
the restriction of the same coordinate twisting section. -/
theorem paired_twist_coordinateCochain_actual
    (R : Type) [CommRing R] (n : ℕ) (j : Fin (n + 1)) :
    paired_twistCochainEquiv R n 1 0 (paired_twist_coordinateCochain R n j) =
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf R n 1)
        (ProjSpace.stdCoverPullback
          (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))))
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n j) 1) := by
  funext s
  change ProjSpace.twistingCochainEquiv R n 1 0
    (GradedModule.cochainTwistEquiv (R := R) (n := n) 1 0
      (paired_twist_coordinateCochain R n j)) s = _
  rw [ProjSpace.twistingCochainEquiv_apply, paired_twist_coordinateCochain_fraction]
  erw [paired_twist_coordinateFraction_section]
  exact (ProjSpace.twistingSectionPresheaf R n 1).res_res _ _ _

end HodgeLean.Foundations.Program.G32Native
