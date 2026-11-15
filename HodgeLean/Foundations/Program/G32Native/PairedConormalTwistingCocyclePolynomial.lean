import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistPolynomial
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafPositiveVanishing

/-! # Polynomial data for zero cocycles of the actual native twisting sheaf -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_GradedModule_nonempty_HEquiv_FD
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
namespace HodgeLean.Foundations.Program.G32Native

/-- The original Laurent monomial complex identifies with the actual
native twisting-sheaf complex, retaining both coordinate maps. -/
def paired_twistCochainEquiv (R : Type) [CommRing R] (n d q : ℕ) :=
  (GradedModule.cochainTwistEquiv (R := R) (n := n) (d : ℤ) q).trans
    (ProjSpace.twistingCochainEquiv R n d q)

/-- Polynomial data generates every degree-zero cocycle of the actual
native nonnegative twisting sheaf. -/
theorem paired_twisting_zero_cocycle_polynomial (R : Type) [CommRing R]
    (n d : ℕ) (hn : 1 ≤ n)
    (c : (ProjSpace.twistingSectionPresheaf R n d).cochain
      (ProjSpace.stdCoverPullback (𝟙 (Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) 0)
    (hc : (ProjSpace.twistingSectionPresheaf R n d).d
      (ProjSpace.stdCoverPullback (𝟙 (Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) 0 c = 0) :
    ∃ g : Twist.Mon n (d : ℤ) ∅ →₀ R,
      paired_twistCochainEquiv R n d 0 (Twist.constSec R (d : ℤ) g) = c := by
  let f := (paired_twistCochainEquiv R n d 0).symm c
  have hf : f ∈ LinearMap.ker (Twist.d R n (d : ℤ) 0) := by
    apply LinearMap.mem_ker.mpr
    apply (paired_twistCochainEquiv R n d 1).injective
    rw [map_zero]
    change ProjSpace.twistingCochainEquiv R n d 1
      (GradedModule.cochainTwistEquiv (d : ℤ) 1 (Twist.d R n (d : ℤ) 0 f)) = 0
    have hcomm := LinearMap.congr_fun
      (GradedModule.cochainTwistEquiv_comm (R := R) (n := n) (d : ℤ) 0) f
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hcomm
    rw [← hcomm]
    rw [ProjSpace.twistingCochainEquiv_d]
    change (ProjSpace.twistingSectionPresheaf R n d).d _ 0
      (paired_twistCochainEquiv R n d 0 f) = 0
    rw [(paired_twistCochainEquiv R n d 0).apply_symm_apply, hc]
  obtain ⟨g, hg⟩ := paired_twist_zero_cocycle_polynomial R (d : ℤ) hn f hf
  exact ⟨g, by rw [hg]; exact (paired_twistCochainEquiv R n d 0).apply_symm_apply c⟩

end HodgeLean.Foundations.Program.G32Native
