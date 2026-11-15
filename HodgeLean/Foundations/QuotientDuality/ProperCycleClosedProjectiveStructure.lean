import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectiveHomologyDimension
import HodgeLean.Foundations.QuotientDuality.ProperCycleReducedMaps

/-! # Original closed subschemes retain actual projective presentations -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.QuotientDuality

/-- An original closed subscheme retains the actual composite projective presentation over the original complex base.
Source: ProjectiveSpace.Presentation; IsClosedImmersion.comp.
HC no distance; AV milestone no distance. -/
theorem properCycle_closed_projective_structure
    (X Y : Over (Spec ↧ℂ)) [IsProjective X.hom] (j : Y ⟶ X)
    [IsClosedImmersion j.left] : IsProjective Y.hom := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := X.hom)
  letI : IsClosedImmersion P.immersion := P.isClosedImmersion
  refine ⟨⟨{
    ambientDimension := P.ambientDimension
    immersion := j.left ≫ P.immersion
    immersion_toBase := ?_ }⟩⟩
  rw [Category.assoc, P.immersion_toBase, Over.w j]

end HodgeLean.Foundations.QuotientDuality
