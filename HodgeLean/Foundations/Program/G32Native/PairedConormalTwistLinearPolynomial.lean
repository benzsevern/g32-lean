import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistLinearCoordinates
import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistingCocyclePolynomial
import Mathlib.LinearAlgebra.Finsupp.LSum

/-! # Linear coefficients of actual native twisting zero cocycles -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
attribute [local instance] MvPolynomial.gradedAlgebra
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual degree-one polynomial data with its original coordinate coefficients. -/
def paired_twist_linearPolynomial (R : Type) [CommRing R] (n : ℕ) :
    (Fin (n + 1) → R) ≃ₗ[R] (Twist.Mon n 1 ∅ →₀ R) :=
  (Finsupp.linearEquivFunOnFinite R R (Fin (n + 1))).symm.trans
    (Finsupp.domLCongr (paired_twist_linearCoordinateEquiv n))

/-- Every actual native degree-one twisting zero cocycle has a vector of
constant linear coefficients in the original coordinate order. -/
theorem paired_twisting_zero_cocycle_linear (R : Type) [CommRing R]
    (n : ℕ) (hn : 1 ≤ n)
    (c : (ProjSpace.twistingSectionPresheaf R n 1).cochain
      (ProjSpace.stdCoverPullback (𝟙 (Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) 0)
    (hc : (ProjSpace.twistingSectionPresheaf R n 1).d
      (ProjSpace.stdCoverPullback (𝟙 (Proj
        (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R)))) 0 c = 0) :
    ∃ v : Fin (n + 1) → R,
      paired_twistCochainEquiv R n 1 0
        (Twist.constSec R 1 (paired_twist_linearPolynomial R n v)) = c := by
  obtain ⟨g, hg⟩ := paired_twisting_zero_cocycle_polynomial R n 1 hn c hc
  exact ⟨(paired_twist_linearPolynomial R n).symm g, by
    rw [(paired_twist_linearPolynomial R n).apply_symm_apply]; exact hg⟩

end HodgeLean.Foundations.Program.G32Native
