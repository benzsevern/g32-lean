import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.ClosedImmersion
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! Complex points of the actual cartesian fibres used by the normal slices. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Topology
namespace HodgeLean.Foundations.Program

/-- A literal cartesian complex-point fibre embeds as exactly the analytic
level set of the specified ambient morphism. -/
theorem s4_q3_cartesian_point_fibre_embedding
    {S X T : Over (Spec ↧ℂ)} (j : S ⟶ X) (h : X ⟶ T) (t : ComplexPoint T)
    (hsquare : IsPullback j.left S.hom h.left t.left) :
    IsClosedEmbedding (Point.map j) ∧
      Set.range (Point.map j) = {x : ComplexPoint X | Point.map h x = t} := by
  letI : IsClosedImmersion t.left := isClosedImmersion_of_comp_eq_id T.hom t.left (Over.w t)
  letI : IsClosedImmersion j.left :=
    MorphismProperty.of_isPullback (P := @IsClosedImmersion) hsquare.flip inferInstance
  refine ⟨ComplexPoint.isClosedEmbedding_map_of_closedImmersion j, ?_⟩
  ext x
  constructor
  · rintro ⟨z, rfl⟩
    apply Over.OverMorphism.ext
    change z.left ≫ j.left ≫ h.left = t.left
    rw [hsquare.w, ← Category.assoc, Over.w z]
    exact Category.id_comp _
  · intro hx
    have he : x.left ≫ h.left = (𝟙 (Spec ↧ℂ)) ≫ t.left := by
      simpa only [Point.map, Over.comp_left, Category.id_comp] using congrArg Over.Hom.left hx
    let z : ComplexPoint S := Over.homMk (hsquare.lift x.left (𝟙 _) he)
      (hsquare.lift_snd x.left (𝟙 _) he)
    refine ⟨z, ?_⟩
    apply Over.OverMorphism.ext
    exact hsquare.lift_fst x.left (𝟙 _) he

end HodgeLean.Foundations.Program
