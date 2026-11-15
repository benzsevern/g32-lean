import HodgeLean.Foundations.QuotientDuality.ProperCycleClosedProjectiveBooleanModel
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ProjectiveCompact

/-! # Global Boolean models retaining actual projective algebraic marks -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- An original projective complex scheme has one compact global Boolean model retaining every specified algebraic closed immersion as its literal Boolean mark.
Source: IsProjective.nonempty_presentation; properCycle_closed_projective_boolean_model; properCycle_projective_closed_boolean_image.
HC no distance; AV milestone no distance. -/
theorem properCycle_projective_marked_boolean_model
    (X : Over (Spec ↧ℂ)) [IsProjective X.hom] {r : ℕ}
    (Z : Fin r → Over (Spec ↧ℂ)) (i : ∀ j, Z j ⟶ X)
    [∀ j, IsClosedImmersion (i j).left] :
    ∃ a : ℕ, ∃ B : s2v_t11b_Formula a, IsCompact B.realize ∧
      ∃ h : ComplexPoint X ≃ₜ B.realize, ∃ b : Fin r → s2v_t11b_Formula a,
        ∀ x j, (h x).val ∈ (b j).realize ↔ x ∈ Set.range (Point.map (i j)) := by
  classical
  let P : ProjectiveSpace.Presentation X.hom :=
    Classical.choice (IsProjective.nonempty_presentation (f := X.hom))
  let e : X ⟶ Over.mk (ProjectiveSpace.toBase (Fin (P.ambientDimension+1)) (Spec ↧ℂ)) :=
    Over.homMk P.immersion P.immersion_toBase
  letI : IsClosedImmersion e.left := P.isClosedImmersion
  letI (j : Fin r) : IsClosedImmersion (i j ≫ e).left :=
    inferInstanceAs (IsClosedImmersion ((i j).left ≫ e.left))
  obtain ⟨B, hcompact, h, hh⟩ := properCycle_closed_projective_boolean_model P.ambientDimension X e
  choose b hb using fun j => properCycle_projective_closed_boolean_image
    P.ambientDimension (Z j) (i j ≫ e)
  refine ⟨_, B, hcompact, h, b, ?_⟩
  intro x j
  rw [hh, hb j]
  constructor
  · rintro ⟨z, hz⟩
    have he : Point.map e (Point.map (i j) z) = Point.map e x := by
      apply (properCycle_projective_boolean_homeomorph P.ambientDimension).injective
      apply Subtype.ext
      simpa only [Point.map_comp_apply] using hz
    exact ⟨z, (isEmbedding_map_of_closedImmersion e).injective he⟩
  · rintro ⟨z, hz⟩
    refine ⟨z, ?_⟩
    dsimp only
    rw [Point.map_comp_apply, hz]

end HodgeLean.Foundations.QuotientDuality
