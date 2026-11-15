import HodgeConjecture.Definitions.AlgebraicGeometry.ProjectiveSpace
import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace HodgeLean.Foundations.Program

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- An actual projective-space presentation transports through an isomorphism of the base. -/
theorem s2_projective_comp_base_iso {X Y Z : Scheme.{0}}
    (f : X ⟶ Y) [IsProjective f] (c : Y ⟶ Z) [IsIso c] : IsProjective (f ≫ c) := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := f)
  letI := P.isClosedImmersion
  let e : ProjectiveSpace (Fin (P.ambientDimension + 1)) Y ⟶
      ProjectiveSpace (Fin (P.ambientDimension + 1)) Z :=
    pullback.map _ _ _ _ c (𝟙 _) (𝟙 _) (by simp) (by simp)
  haveI : IsIso e := by dsimp only [e]; infer_instance
  refine ⟨⟨⟨P.ambientDimension, P.immersion ≫ e, ?_⟩⟩⟩
  have he : e ≫ ProjectiveSpace.toBase _ Z = ProjectiveSpace.toBase _ Y ≫ c := by
    simp only [e, ProjectiveSpace.toBase, pullback.lift_fst]
  rw [Category.assoc, he, ← Category.assoc, P.immersion_toBase]

/-- An actual projective-space presentation transports through an isomorphism of the source. -/
theorem s2_projective_precomp_iso {X Y Z : Scheme.{0}}
    (c : X ⟶ Y) [IsIso c] (f : Y ⟶ Z) [IsProjective f] : IsProjective (c ≫ f) := by
  obtain ⟨P⟩ := IsProjective.nonempty_presentation (f := f)
  letI := P.isClosedImmersion
  refine ⟨⟨⟨P.ambientDimension, c ≫ P.immersion, ?_⟩⟩⟩
  rw [Category.assoc, P.immersion_toBase]

end HodgeLean.Foundations.Program
