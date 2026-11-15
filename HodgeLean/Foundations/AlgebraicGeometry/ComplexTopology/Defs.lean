import HodgeConjecture.Definitions.AlgebraicGeometry.ComplexPoint.Basic
import Mathlib.Topology.Homotopy.Contractible
import Mathlib.Algebra.MvPolynomial.Eval

/-! Polynomial coordinate carriers for the actual complex-point topology.
HC no distance; AV milestone no distance. -/

noncomputable section
namespace HodgeLean.Foundations.ComplexTopology

/-- The Euclidean common zero set of a finite list of complex polynomials.
Source: Bochnak, Coste, Roy, Real Algebraic Geometry, §2.1. -/
def zeroSet {n m : ℕ} (p : Fin m → MvPolynomial (Fin n) ℂ) :
    Set (Fin n → ℂ) := {z | ∀ j, MvPolynomial.eval z (p j) = 0}

example : (fun _ : Fin 1 => (0 : ℂ)) ∈
    zeroSet (fun _ : Fin 1 => (MvPolynomial.X (0 : Fin 1)) ^ 2) := by
  intro j
  simp [MvPolynomial.eval_pow]

end HodgeLean.Foundations.ComplexTopology
