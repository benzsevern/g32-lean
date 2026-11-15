import HodgeLean.Foundations.Program.SchoenCycleSymmetricPoints
import HodgeLean.Foundations.Program.SchoenCycleDivisorEnumeration

/-! # Literal divisor evaluations of specified ordered quotient lifts -/
noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint HodgeLean.Adapters
open scoped BigOperators
namespace HodgeLean.Foundations.Program.G32Native
open HodgeLean.Foundations.Program

/-- An ordered lift with the exact integer divisor evaluates to the original
unordered divisor point in the specified symmetric quotient.
Source: Schoen, Compositio Mathematica 65 (1988), §2. -/
theorem residual_quotient_divisor_lift_evaluation
    (Z B : Over (Spec ↧ℂ)) (n : ℕ) (γ : g3_power Z n ⟶ B)
    (hγ : ∀ σ, s2_permute Z n σ ≫ γ = γ)
    (D : ComplexPoint Z →₀ ℤ) (hD : ∀ q, 0 ≤ D q) (hn : b4c_deg D = (n : ℤ))
    (x : ComplexPoint (g3_power Z n))
    (hx : D = ∑ j, Finsupp.single (Point.map (g3_proj Z n j) x) (1 : ℤ)) :
    Point.map γ x = s2e_symmetricQuotientEvaluation n γ (s2e_divisorSym D hD hn) := by
  classical
  let t := fun j => Point.map (g3_proj Z n j) x
  have he := s2e_symmetricQuotientEvaluation_eq n γ hγ _ t
    (s2e_divisor_tuple_enumeration D hD hn t hx)
  exact (he.trans (congrArg (Point.map γ) (s2e_lift_coordinates n x))).symm

#print axioms residual_quotient_divisor_lift_evaluation
end HodgeLean.Foundations.Program.G32Native
