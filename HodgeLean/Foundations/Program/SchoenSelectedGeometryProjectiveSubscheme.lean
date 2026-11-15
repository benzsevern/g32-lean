import HodgeLean.Foundations.Program.SchoenSelectedGeometryProjectiveDimension

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting a projective presentation to a closed subscheme gives a projective presentation.
Source: Hartshorne, Algebraic Geometry, II.4, composition of algebraic closed immersions. -/
theorem s0_projective_comp_closedImmersion {X Y S : Scheme.{0}}
    (i : Y ⟶ X) (f : X ⟶ S) [IsClosedImmersion i] [IsProjective f] :
    IsProjective (i ≫ f) := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := f)
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  exact ⟨⟨{ ambientDimension := P.ambientDimension
            immersion := i ≫ P.immersion
            immersion_toBase := by rw [Category.assoc, P.immersion_toBase] }⟩⟩

#print axioms s0_projective_comp_closedImmersion
end HodgeLean.Foundations.Program
