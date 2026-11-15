import HodgeLean.Foundations.Program.G32Native.ConormalEvaluationContinuity

/-! # Finite coordinates for the retained homogeneous coefficient covectors -/
noncomputable section
set_option maxHeartbeats 200000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint Bundle
namespace HodgeLean.Foundations.Program.G32Native

/-- Ordered dual coordinates on the original homogeneous coefficient space.
Source: ACGH, Geometry of Algebraic Curves I, IV.1, ordered form coordinates. -/
def coefficientCoordinateEquiv (k : ℕ) :
    Module.Dual ℂ (Fin (k + 1) → ℂ) ≃ₗ[ℂ] (Fin (k + 1) → ℂ) :=
  (Pi.basisFun ℂ (Fin (k + 1))).dualBasis.equivFun

/-- The ordered coordinate is evaluation on the original coordinate vector. -/
theorem coefficientCoordinateEquiv_apply (k : ℕ)
    (a : Module.Dual ℂ (Fin (k + 1) → ℂ)) (i : Fin (k + 1)) :
    coefficientCoordinateEquiv k a i = a (Pi.single i 1) := by
  exact (Module.Basis.dualBasis_equivFun (Pi.basisFun ℂ _) a i).trans
    (congrArg a (Pi.basisFun_apply ℂ (Fin (k + 1)) i))

#print axioms coefficientCoordinateEquiv
#print axioms coefficientCoordinateEquiv_apply
/-- Passing through the ordered coefficient dual retains every original coordinate. -/
theorem coefficientCoordinateEquiv_coefficientDual (k : ℕ) (v : Fin (k + 1) → ℂ) :
    coefficientCoordinateEquiv k (coefficientDual k v) = v := by
  ext i
  rw [coefficientCoordinateEquiv_apply]
  change (∑ j : Fin (k + 1), (Pi.single i (1 : ℂ) : Fin (k + 1) → ℂ) j * v j) = v i
  simp only [Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]

#print axioms coefficientCoordinateEquiv_coefficientDual
end HodgeLean.Foundations.Program.G32Native
