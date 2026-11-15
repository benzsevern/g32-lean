import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.SmoothCoordinates

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- An actual etale morphism to the smooth retained base gives the same relative dimension on its actual source over the original complex structure map.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
EGA IV, 17.11.1. -/
theorem s2e_etale_smooth_source
    (X Y : Over (Spec ↧ℂ)) (n : ℕ) [SmoothOfRelativeDimension n Y.hom]
    (f : X ⟶ Y) [Etale f.left] : SmoothOfRelativeDimension n X.hom := by
  rw [← f.w]
  simpa only [zero_add] using
    (inferInstance : SmoothOfRelativeDimension (0 + n) (f.left ≫ Y.hom))

#print axioms s2e_etale_smooth_source
end HodgeLean.Foundations.Program
