import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Actual base change from schemes over the terminal scheme to schemes over a specified base. -/
def s2_terminalBaseChange (S : Scheme.{0}) : Scheme.{0} ⥤ Over S where
  obj X := Over.mk (pullback.fst (terminal.from S) (terminal.from X))
  map {X Y} f := Over.homMk (pullback.map
    (terminal.from S) (terminal.from X) (terminal.from S) (terminal.from Y)
    (𝟙 S) f (𝟙 (terminal Scheme)) (terminal.hom_ext _ _) (terminal.hom_ext _ _))
      (by simp [pullback.map])
  map_id X := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [pullback.map]
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;> simp [pullback.map, Category.assoc]

/-- Actual terminal base change preserves the underlying map to the second product factor. -/
theorem s2_terminalBaseChange_map_snd (S : Scheme.{0}) {X Y : Scheme.{0}} (f : X ⟶ Y) :
    ((s2_terminalBaseChange S).map f).left ≫
      pullback.snd (terminal.from S) (terminal.from Y) =
        pullback.snd (terminal.from S) (terminal.from X) ≫ f := by
  simp only [s2_terminalBaseChange, Over.homMk_left, pullback.map, pullback.lift_snd]

/-- Actual terminal base change preserves scheme closed immersions. -/
theorem s2_terminalBaseChange_map_isClosedImmersion (S : Scheme.{0})
    {X Y : Scheme.{0}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsClosedImmersion ((s2_terminalBaseChange S).map f).left := by
  letI : MorphismProperty.IsStableUnderComposition @IsClosedImmersion :=
    MorphismProperty.IsMultiplicative.toIsStableUnderComposition
  change IsClosedImmersion (pullback.map
    (terminal.from S) (terminal.from X) (terminal.from S) (terminal.from Y)
    (𝟙 S) f (𝟙 (terminal Scheme)) (terminal.hom_ext _ _) (terminal.hom_ext _ _))
  exact MorphismProperty.pullbackMap (P := @IsClosedImmersion) (i₁ := 𝟙 S) (i₂ := f)
    (by infer_instance) (by infer_instance) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

end HodgeLean.Foundations.Program
