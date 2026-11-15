import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistLinearPolynomial
import HodgeLean.Foundations.Program.G32Native.PairedConormalTwistPolynomialInjective

/-! # Fidelity of constant linear coefficients in the actual twisting complex -/

noncomputable section
open AlgebraicGeometry
open AlgebraicCurves.Cohomology.Cech.Proofs.ProjSpaceCech_Twist_finite_cohomology
open ProjSpaceCech
namespace HodgeLean.Foundations.Program.G32Native

/-- The actual native degree-one twisting cocycle retains its original
coefficient vector, rejecting sign, scale, zero and index mutations. -/
theorem paired_twisting_linear_coefficients_injective (R : Type) [CommRing R] (n : ℕ) :
    Function.Injective (fun v : Fin (n + 1) → R =>
      paired_twistCochainEquiv R n 1 0
        (Twist.constSec R 1 (paired_twist_linearPolynomial R n v))) :=
  (paired_twistCochainEquiv R n 1 0).injective.comp
    ((paired_twist_constSec_injective R n 1).comp
      (paired_twist_linearPolynomial R n).injective)

end HodgeLean.Foundations.Program.G32Native
