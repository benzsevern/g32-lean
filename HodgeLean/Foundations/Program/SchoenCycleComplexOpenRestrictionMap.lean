import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual restriction of a scheme morphism to source and target opens respects their original complex structure maps and their inclusion diagram.
Source: Schoen, Compositio Mathematica 65 (1988), Lemma 2.2, printed p. 13;
Hartshorne, Algebraic Geometry, II.2. -/
theorem s2e_complex_open_restriction_map
    (X Y : Over (Spec ↧ℂ)) (f : X ⟶ Y)
    (U : Y.left.Opens) (V : X.left.Opens) (hV : V ≤ f.left ⁻¹ᵁ U) :
    ∃ r : ComplexPoint.openScheme X V ⟶ ComplexPoint.openScheme Y U,
      r.left = f.left.resLE U V hV ∧
      r ≫ ComplexPoint.openInclusion Y U = ComplexPoint.openInclusion X V ≫ f := by
  have hw : f.left.resLE U V hV ≫ (U.ι ≫ Y.hom) = V.ι ≫ X.hom := by
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, f.w]
  refine ⟨Over.homMk (f.left.resLE U V hV) hw, rfl, ?_⟩
  apply Over.OverMorphism.ext
  exact Scheme.Hom.resLE_comp_ι f.left hV

#print axioms s2e_complex_open_restriction_map
end HodgeLean.Foundations.Program
