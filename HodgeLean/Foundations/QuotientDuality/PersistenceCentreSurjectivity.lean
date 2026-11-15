import HodgeLean.Foundations.QuotientDuality.PersistenceCentreProjection

/-! Actual exceptional-to-centre point lifts from ambient transition point lifts. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_centre_projection_point_surjective
    {X Y B' B K : Over (Spec ↧ℂ)}
    (β : X ⟶ B') (βprev : Y ⟶ B) (b : B' ⟶ B) (k : K ⟶ B)
    (w : X ⟶ Y) (hw : w ≫ βprev = β ≫ b)
    (hsurj : Function.Surjective (Point.map w)) :
    Function.Surjective (Point.map (persistenceCentreProjection β βprev b k w hw)) := by
  intro z
  obtain ⟨x, hx⟩ := hsurj (Point.map (pullback.fst βprev k) z)
  change x ≫ w = z ≫ pullback.fst βprev k at hx
  have heq : (x ≫ β) ≫ b = (z ≫ pullback.snd βprev k) ≫ k := by
    rw [Category.assoc, ← hw, ← Category.assoc, hx,
      Category.assoc, pullback.condition, ← Category.assoc]
  let e : ComplexPoint (pullback b k) :=
    pullback.lift (x ≫ β) (z ≫ pullback.snd βprev k) heq
  let t : ComplexPoint (s2b_preimage β (pullback.fst b k)) :=
    pullback.lift x e (by simp only [e, pullback.lift_fst])
  refine ⟨t, ?_⟩
  change t ≫ persistenceCentreProjection β βprev b k w hw = z
  apply pullback.hom_ext
  · simpa only [t, persistenceCentreProjection, Category.assoc,
      pullback.lift_fst, pullback.lift_fst_assoc] using hx
  · simp only [t, e, persistenceCentreProjection, Category.assoc,
      pullback.lift_snd, pullback.lift_snd_assoc]

end HodgeLean.Foundations.QuotientDuality
