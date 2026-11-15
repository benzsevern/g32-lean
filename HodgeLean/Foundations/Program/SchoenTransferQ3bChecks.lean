import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.BoundaryDefs

/-! A surviving prime in the removed set detects an invalid boundary bound.
HC no distance; AV milestone no distance. -/

noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace HodgeLean.Adapters
open AlgebraicGeometry.SingularCycles
open scoped Classical
namespace HodgeLean.Foundations.Program
private abbrev P := Spec (CommRingCat.of ℂ)
private def x : P := Point.underlying (𝟙 (Over.mk (𝟙 P)) : ComplexPoint (Over.mk (𝟙 P)))
private def weights : P →₀ ℚ := Finsupp.single x (2 : ℚ)
private theorem weights_cycle : collectedCycle weights =
    Function.locallyFinsuppWithin.single x (2 : ℚ) := by
  classical
  simp [collectedCycle, weights]

/-- Removing a surviving component fails the higher-coheight boundary requirement.
Source: Fulton, Intersection Theory, second edition, §19.1; Mathlib Order.coheight_eq_zero. -/
theorem s4_q3b_boundary_comparison_falsification :
    x ∈ sourceBoundary (𝟙 P) (𝟙 P) ⊤ weights ∧
      ¬ ((1 : ℕ) : ℕ∞) ≤ Order.coheight x := by
  constructor
  · change x ∈ a3b4a_classAlgebraicSupport (𝟙 P) (collectedCycle weights) ∧ _
    constructor
    · rw [weights_cycle]
      simp [a3b4a_classAlgebraicSupport]
    · trivial
  · rw [Order.IsMax.coheight_eq_zero
      (show IsMax x from fun _ _ => le_of_eq (Subsingleton.elim _ _))]
    norm_num

example := s4_q3b_boundary_comparison_falsification
#print axioms s4_q3b_boundary_comparison_falsification
end HodgeLean.Foundations.Program
