import HodgeLean.Foundations.Program.SchoenTransferQ3FlatOpen
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-! The actual finite flat map on compatible cartesian normal slices. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Fibres of compatible tangential coordinate maps give k-dimensional
smooth slices, and their specified map is the finite flat base change of q. -/
theorem s4_q3_cartesian_slices_finite_flat_smooth
    {X W T B : Scheme.{0}} (q : X ⟶ W) [IsFinite q] [Flat q]
    (h : W ⟶ T) (t : B ⟶ T) (k : ℕ)
    [SmoothOfRelativeDimension k h] [SmoothOfRelativeDimension k (q ≫ h)] :
    IsFinite (pullback.snd q (pullback.fst h t)) ∧
      Flat (pullback.snd q (pullback.fst h t)) ∧
      SmoothOfRelativeDimension k (pullback.snd h t) ∧
      SmoothOfRelativeDimension k
        (pullback.snd q (pullback.fst h t) ≫ pullback.snd h t) := by
  have hsquare := (IsPullback.of_hasPullback q (pullback.fst h t)).paste_vert
    (IsPullback.of_hasPullback h t)
  exact ⟨inferInstance, inferInstance, inferInstance,
    MorphismProperty.of_isPullback (P := @SmoothOfRelativeDimension k) hsquare inferInstance⟩

/-- Compatible smooth tangential maps give the actual finite flat maps on
smooth cartesian slices, without requiring a global relative-dimension value. -/
theorem s4_q3_cartesian_slices_finite_flat_of_smooth
    {X W T B : Scheme.{0}} (q : X ⟶ W) [IsFinite q] [Flat q]
    (h : W ⟶ T) (t : B ⟶ T) [Smooth h] [Smooth (q ≫ h)] :
    IsFinite (pullback.snd q (pullback.fst h t)) ∧
      Flat (pullback.snd q (pullback.fst h t)) ∧
      Smooth (pullback.snd h t) ∧
      Smooth (pullback.snd q (pullback.fst h t) ≫ pullback.snd h t) := by
  have hsquare := (IsPullback.of_hasPullback q (pullback.fst h t)).paste_vert
    (IsPullback.of_hasPullback h t)
  exact ⟨inferInstance, inferInstance, inferInstance,
    MorphismProperty.of_isPullback (P := @Smooth) hsquare inferInstance⟩

end HodgeLean.Foundations.Program
