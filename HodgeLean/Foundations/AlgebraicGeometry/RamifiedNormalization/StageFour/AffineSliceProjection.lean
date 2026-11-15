import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceProjectionProperness
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.SliceProjectionSurjectivity
import HodgeLean.Foundations.AlgebraicGeometry.RamifiedNormalization.StageFour.FiniteProjectionProperness

noncomputable section
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits
open scoped OnePoint
namespace AlgebraicGeometry.RamifiedNormalization.StageFour

/-- The actual covering slice away from the second retained branch has a proper surjective projection in the same finite sphere coordinate. -/
theorem affine_slice_projection_proper_surjective
    {W B' B : Over (Spec ↧ℂ)} [IsSeparated B.hom] [IsSeparated B'.hom]
    [CompactSpace (ComplexPoint W)] [CompactSpace (ComplexPoint B')]
    [T2Space (ComplexPoint B')]
    (β : W ⟶ B') (b : B' ⟶ B) (x : ComplexPoint B)
    (hβ : Function.Surjective (Point.map β))
    (D : B'.left.IdealSheafData) (vE : ComplexPoint (exceptionalSlice b x) ≃ₜ OnePoint ℂ)
    (hendpoint : ∀ z : ComplexPoint (exceptionalSlice b x),
      (Point.map (pullback.fst b x) z).left (IsLocalRing.closedPoint ℂ) ∈ D.support ↔ vE z = ∞) :
    ∃ p : {z : ComplexPoint (coveringSlice β b x) //
        (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
          (IsLocalRing.closedPoint ℂ) ∉ D.support} → ℂ,
      IsProperMap p ∧ Function.Surjective p ∧
      ∀ z, (p z : OnePoint ℂ) = vE (Point.map (sliceProjection β b x) z.val) := by
  let P := Point.map (sliceProjection β b x)
  have hP : IsProperMap P := covering_slice_projection_proper β b x
  have hPs : Function.Surjective P := slice_projection_points_surjective β b x hβ
  let R : ComplexPoint (coveringSlice β b x) → OnePoint ℂ := fun z => vE (P z)
  have hR : IsProperMap R := vE.isProperMap.comp hP
  have hRs : Function.Surjective R := vE.surjective.comp hPs
  obtain ⟨p, hp, hps, hcoord⟩ := proper_finite_sphere_projection R hR hRs
  let H : {z : ComplexPoint (coveringSlice β b x) //
        (Point.map (pullback.fst b x) (Point.map (sliceProjection β b x) z)).left
          (IsLocalRing.closedPoint ℂ) ∉ D.support} ≃ₜ
      {z : ComplexPoint (coveringSlice β b x) // R z ≠ ∞} :=
    (Homeomorph.refl _).subtype (fun z => by
      change ¬ (Point.map (pullback.fst b x) (P z)).left (IsLocalRing.closedPoint ℂ) ∈ D.support ↔
        ¬ vE (P z) = ∞
      exact not_congr (hendpoint (P z)))
  exact ⟨p ∘ H, hp.comp H.isProperMap, hps.comp H.surjective, fun z => hcoord (H z)⟩

end AlgebraicGeometry.RamifiedNormalization.StageFour
