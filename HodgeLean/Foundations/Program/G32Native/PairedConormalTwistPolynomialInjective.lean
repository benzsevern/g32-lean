import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistPolynomial

/-! # Coefficient fidelity of homogeneous polynomial zero cocycles -/

noncomputable section
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
namespace HodgeLean.Foundations.Program.G32Native

/-- Restricting homogeneous polynomial data to the native zero cocycle
retains every coefficient, rejecting zero and scale mutations. -/
theorem paired_twist_constSec_injective (R : Type*) [CommRing R] (n : ℕ) (d : ℤ) :
    Function.Injective (Twist.constSec R (n := n) d) := by
  intro g h he
  apply Finsupp.mapDomain_injective (Twist.Mon.incl_injective n d (Finset.empty_subset
    (Idx.img n (Twist.vtx 0))))
  exact congrFun he (Twist.vtx 0)

end HodgeLean.Foundations.Program.G32Native
