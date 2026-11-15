import HodgeLean.Foundations.Program.SchoenCycleQuotientAffineFiniteType
import HodgeLean.Foundations.Program.SchoenCycleComplexFiniteTypeCriterion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Finite surjective descent preserves local finite type over the complex base for the actual integral schemes.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Atiyah–Macdonald, Introduction to Commutative Algebra, Proposition 7.8. -/
theorem s2e_finite_surjective_locallyOfFiniteType
    (X Y : Over (Spec ↧ℂ)) [IsIntegral X.left] [IsIntegral Y.left]
    [LocallyOfFiniteType X.hom] (q : X ⟶ Y) [IsFinite q.left] [Surjective q.left] :
    LocallyOfFiniteType Y.hom := by
  apply s2e_locallyOfFiniteType_of_complex_affine_sections Y
  intro U hU
  exact s2e_finite_surjective_affine_sections_finiteType X Y q U hU

#print axioms s2e_finite_surjective_locallyOfFiniteType
end HodgeLean.Foundations.Program
