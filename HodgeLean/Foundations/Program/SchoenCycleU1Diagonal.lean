import HodgeLean.Foundations.Program.SchoenCycleStep1Symmetric
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified
import Mathlib.AlgebraicGeometry.Morphisms.IsIso
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-! # Finite unramified maps separated by complex points -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.Program

/-- Complex-point separation makes the diagonal of a finite map surjective.
Source: HodgeLean, `s2e_step1_surjective_of_complexPoint_surjective`;
Hartshorne, Algebraic Geometry, II.4, diagonal criterion for separatedness. -/
theorem s2e_u1_finite_diagonal_surjective
    (X Y : Over (Spec ↧ℂ)) [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom]
    (f : X ⟶ Y) [IsFinite f.left]
    (hinj : Function.Injective (Point.map f)) : Surjective (pullback.diagonal f.left) := by
  let P : Over (Spec ↧ℂ) := Over.mk (pullback.fst f.left f.left ≫ X.hom)
  letI : LocallyOfFiniteType P.hom := by dsimp [P]; infer_instance
  let p₁ : P ⟶ X := Over.homMk (pullback.fst f.left f.left) rfl
  let p₂ : P ⟶ X := Over.homMk (pullback.snd f.left f.left) (by
    change pullback.snd f.left f.left ≫ X.hom = pullback.fst f.left f.left ≫ X.hom
    rw [← Over.w f, ← Category.assoc, ← pullback.condition, Category.assoc])
  let d : X ⟶ P := Over.homMk (pullback.diagonal f.left) (by simp [P])
  letI : IsClosedImmersion d.left := by
    change IsClosedImmersion (pullback.diagonal f.left)
    infer_instance
  have hd : Function.Surjective (Point.map d) := by
    intro z
    have hp : Point.map p₁ z = Point.map p₂ z := by
      apply hinj
      apply Over.OverMorphism.ext
      change z.left ≫ pullback.fst f.left f.left ≫ f.left =
        z.left ≫ pullback.snd f.left f.left ≫ f.left
      rw [pullback.condition]
    refine ⟨Point.map p₁ z, ?_⟩
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · simp only [Point.map, Over.comp_left, d, p₁, Over.homMk_left, Category.assoc,
        pullback.diagonal_fst, Category.comp_id]
    · change z.left ≫ pullback.fst f.left f.left ≫ pullback.diagonal f.left ≫
          pullback.snd f.left f.left = z.left ≫ pullback.snd f.left f.left
      rw [pullback.diagonal_snd, Category.comp_id]
      exact congrArg Over.Hom.left hp
  exact s2e_step1_surjective_of_complexPoint_surjective X P d hd

end HodgeLean.Foundations.Program
