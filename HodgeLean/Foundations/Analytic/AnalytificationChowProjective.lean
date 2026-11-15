import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import HodgeLean.Foundations.SegreProjective

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open ProjectiveSpace

namespace HodgeLean.Foundations.Analytic

/-- A closed immersion followed by a projective morphism is projective.
Source: EGA II, Proposition 5.5.5 (ii). -/
theorem AnalytificationChow_isProjective_comp_of_isClosedImmersion
    {X Y T : Scheme} (i : X ⟶ Y) (f : Y ⟶ T) [IsClosedImmersion i] [IsProjective f] :
    IsProjective (i ≫ f) := by
  let P := Classical.choice (IsProjective.nonempty_presentation (f := f))
  let _ : IsClosedImmersion P.immersion := P.isClosedImmersion
  refine ⟨⟨
    { ambientDimension := P.ambientDimension
      immersion := i ≫ P.immersion
      immersion_toBase := by rw [Category.assoc, P.immersion_toBase] }⟩⟩

/-- A fibre product of projective morphisms is projective.
Source: Hartshorne, *Algebraic Geometry*, Exercises II.4.9 and II.5.11. -/
theorem AnalytificationChow_isProjective_pullback
    {X Y T : Scheme.{0}} (f : X ⟶ T) (g : Y ⟶ T) [IsProjective f] [IsProjective g] :
    IsProjective (pullback.fst f g ≫ f) :=
  HodgeLean.Foundations.spec_g3c_isProjective_pullback f g

end HodgeLean.Foundations.Analytic
