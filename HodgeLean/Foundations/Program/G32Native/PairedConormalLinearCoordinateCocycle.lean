import HodgeLean.Foundations.Program.G32Native.PairedConormalCoordinateCocycle
import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistLinearPolynomial
import Mathlib.LinearAlgebra.StdBasis

/-! # The actual coordinate-section expansion of a homogeneous linear cocycle -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The original coefficient at index j gives precisely the same coordinate monomial. -/
theorem paired_twist_linearPolynomial_single (R : Type) [CommRing R]
    (n : ℕ) (j : Fin (n + 1)) :
    paired_twist_linearPolynomial R n (Pi.single j 1) =
      Finsupp.single (paired_twist_coordinateMonomial n j) 1 := by
  classical
  rw [paired_twist_linearPolynomial, LinearEquiv.trans_apply,
    Finsupp.linearEquivFunOnFinite_symm_single, Finsupp.domLCongr_single]
  rfl

/-- Every original linear coefficient vector gives the same linear
combination of the actual coordinate section cocycles. -/
theorem paired_twisting_linear_cocycle_coordinates
    (R : Type) [CommRing R] (n : ℕ) (v : Fin (n + 1) → R) :
    paired_twistCochainEquiv R n 1 0
      (Twist.constSec R 1 (paired_twist_linearPolynomial R n v)) =
      ∑ j : Fin (n + 1), v j •
        pairedCechRestriction (ProjSpace.twistingSectionPresheaf R n 1)
          (ProjSpace.stdCoverPullback
            (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))))
          (tensorPowSection (ProjSpace.twistingCoordinateSection R n j) 1) := by
  classical
  have hv : (∑ j, v j • (Pi.single j 1 : Fin (n + 1) → R)) = v := by
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply] using
      (Pi.basisFun R (Fin (n + 1))).sum_repr v
  have h := congrArg (fun w => paired_twistCochainEquiv R n 1 0
    (Twist.constSec R 1 (paired_twist_linearPolynomial R n w))) hv
  have hj (j : Fin (n + 1)) : paired_twistCochainEquiv R n 1 0
      (Twist.constSec R 1 (Finsupp.single (paired_twist_coordinateMonomial n j) 1)) =
      pairedCechRestriction (ProjSpace.twistingSectionPresheaf R n 1)
        (ProjSpace.stdCoverPullback
          (𝟙 (Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R))))
        (tensorPowSection (ProjSpace.twistingCoordinateSection R n j) 1) :=
    paired_twist_coordinateCochain_actual R n j
  simp only [map_sum, LinearEquiv.map_smul, LinearMap.map_smul, paired_twist_linearPolynomial_single,
    hj] at h
  exact h.symm

end HodgeLean.Foundations.Program.G32Native
