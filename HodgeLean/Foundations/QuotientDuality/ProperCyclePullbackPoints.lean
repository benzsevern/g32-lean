import HodgeLean.Foundations.QuotientDuality.ProperCycleAffineChartProjectiveImage

/-! # Actual complex points in original scheme pullbacks -/

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
namespace HodgeLean.Foundations.QuotientDuality

/-- The original scheme pullback retains its structure map to the original complex base.
Source: CategoryTheory.Limits.pullback.fst.
HC no distance; AV milestone no distance. -/
def properCycle_over_pullback {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Z ⟶ Y) :
    Over (Spec ↧ℂ) := Over.mk (Limits.pullback.fst f.left g.left ≫ X.hom)

/-- First projection of the original scheme pullback over the complex base.
Source: CategoryTheory.Limits.pullback.fst.
HC no distance; AV milestone no distance. -/
def properCycle_over_pullback_fst {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Z ⟶ Y) :
    properCycle_over_pullback f g ⟶ X :=
  Over.homMk (Limits.pullback.fst f.left g.left) rfl

/-- Second projection of the original scheme pullback over the complex base.
Source: CategoryTheory.Limits.pullback.condition.
HC no distance; AV milestone no distance. -/
def properCycle_over_pullback_snd {X Y Z : Over (Spec ↧ℂ)} (f : X ⟶ Y) (g : Z ⟶ Y) :
    properCycle_over_pullback f g ⟶ Z :=
  Over.homMk (Limits.pullback.snd f.left g.left) (by
    change Limits.pullback.snd f.left g.left ≫ Z.hom =
      Limits.pullback.fst f.left g.left ≫ X.hom
    rw [← Over.w g, ← Over.w f, ← Category.assoc, ← Category.assoc,
      Limits.pullback.condition])

/-- Compatible original complex points lift to the actual scheme pullback with both specified projection values.
Source: CategoryTheory.Limits.pullback.lift; Limits.pullback.lift_fst; Limits.pullback.lift_snd.
HC no distance; AV milestone no distance. -/
theorem properCycle_over_pullback_point_lift {X Y Z : Over (Spec ↧ℂ)}
    (f : X ⟶ Y) (g : Z ⟶ Y) (x : ComplexPoint X) (z : ComplexPoint Z)
    (h : Point.map f x = Point.map g z) :
    ∃ w : ComplexPoint (properCycle_over_pullback f g),
      Point.map (properCycle_over_pullback_fst f g) w = x ∧
      Point.map (properCycle_over_pullback_snd f g) w = z := by
  have he : x.left ≫ f.left = z.left ≫ g.left := congrArg (fun p => p.left) h
  let w : ComplexPoint (properCycle_over_pullback f g) :=
    Over.homMk (Limits.pullback.lift x.left z.left he) (by
      change Limits.pullback.lift x.left z.left he ≫
        (Limits.pullback.fst f.left g.left ≫ X.hom) = 𝟙 _
      rw [← Category.assoc, Limits.pullback.lift_fst, Over.w x]
      rfl)
  refine ⟨w, ?_, ?_⟩
  · apply Over.OverMorphism.ext
    exact Limits.pullback.lift_fst _ _ _
  · apply Over.OverMorphism.ext
    exact Limits.pullback.lift_snd _ _ _

end HodgeLean.Foundations.QuotientDuality
