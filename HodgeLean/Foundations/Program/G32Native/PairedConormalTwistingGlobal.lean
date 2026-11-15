import HodgeLean.Foundations.Program.G32Native.PairedConormalCechGlobalEquiv
import HodgeLean.Ported.NYLL.SchemeTheory.ProjectiveSpace.TwistingSheafCechComparison

/-! # Native global twisting sections and the actual homogeneous fraction complex -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry ProjSpaceCech
namespace HodgeLean.Foundations.Program.G32Native
attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance] GradedModule.acg GradedModule.modR GradedModule.Frac.setoid
  GradedModule.sec.instAddCommGroup GradedModule.sec.instModule
  GradedModule.H.addCommGroup GradedModule.H.module
variable (R : Type) [CommRing R] (k d : ℕ)
local notation "P" => Proj (MvPolynomial.homogeneousSubmodule (Fin (k + 1)) R)
local notation "F" => ProjSpace.twistingSectionPresheaf R k d
local notation "K" => ProjSpace.stdCoverPullback (𝟙 P)

/-- The original section comparison restricts to the kernels of the original zero differentials. -/
def conormalTwistingZeroCocycleEquiv :
    LinearMap.ker (GradedModule.d (GradedModule.FD R k d) 0) ≃ₗ[R] (F).H0 K where
  toFun c := ⟨ProjSpace.twistingCochainEquiv R k d 0 c.val, by
    change (F).d K 0 ((ProjSpace.twistingCochainEquiv R k d 0) c.val) = 0
    rw [← ProjSpace.twistingCochainEquiv_d, c.property, map_zero]⟩
  invFun c := ⟨(ProjSpace.twistingCochainEquiv R k d 0).symm c.val, by
    change GradedModule.d (GradedModule.FD R k d) 0 _ = 0
    apply (ProjSpace.twistingCochainEquiv R k d 1).injective
    rw [ProjSpace.twistingCochainEquiv_d, LinearEquiv.apply_symm_apply, c.property, map_zero]⟩
  left_inv c := Subtype.ext ((ProjSpace.twistingCochainEquiv R k d 0).symm_apply_apply c.val)
  right_inv c := Subtype.ext ((ProjSpace.twistingCochainEquiv R k d 0).apply_symm_apply c.val)
  map_add' c c' := Subtype.ext (map_add (ProjSpace.twistingCochainEquiv R k d 0) c.val c'.val)
  map_smul' r c := Subtype.ext (map_smul (ProjSpace.twistingCochainEquiv R k d 0) r c.val)

/-- Actual global twisting sections are identified with homogeneous degree-zero cohomology. -/
def conormalTwistingGlobalEquiv :
    (F).obj ⊤ ≃ₗ[R] GradedModule.H (GradedModule.FD R k d) 0 :=
  (conormalCechGlobalEquiv ((𝟙 P) ≫ ProjSpace.π R k) K
    ((ProjSpace.twistingSheaf R k).tensorPow d)).trans
      (conormalTwistingZeroCocycleEquiv R k d).symm

end HodgeLean.Foundations.Program.G32Native
