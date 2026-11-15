import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.Defs

noncomputable section
set_option Elab.async false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- Surjectivity of the original covering on complex points survives restriction to the actual exceptional slice. -/
theorem slice_projection_points_surjective
    {W B' B : Over (Spec ↧ℂ)} (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B)
    (hβ : Function.Surjective (Point.map β)) :
    Function.Surjective (Point.map (sliceProjection β b x)) := by
  intro z
  obtain ⟨w, hw⟩ := hβ (Point.map (pullback.fst b x) z)
  let q : ComplexPoint (coveringSlice β b x) := pullback.lift w z hw
  refine ⟨q, ?_⟩
  change pullback.lift w z hw ≫ pullback.snd β (pullback.fst b x) = z
  exact pullback.lift_snd _ _ _

end AlgebraicGeometry.RamifiedNormalization.StageFour
