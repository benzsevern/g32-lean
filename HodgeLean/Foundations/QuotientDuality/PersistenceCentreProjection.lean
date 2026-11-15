import HodgeLean.Foundations.QuotientDuality.PersistenceSupport

/-! The actual exceptional-to-centre map of covering preimages. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The map from the exceptional preimage to the preceding centre preimage. -/
def persistenceCentreProjection
    {X Y B' B K : Over (Spec ↧ℂ)}
    (β : X ⟶ B') (βprev : Y ⟶ B) (b : B' ⟶ B) (k : K ⟶ B)
    (w : X ⟶ Y) (hw : w ≫ βprev = β ≫ b) :
    s2b_preimage β (pullback.fst b k) ⟶ s2b_preimage βprev k :=
  pullback.lift (pullback.fst β (pullback.fst b k) ≫ w)
    (pullback.snd β (pullback.fst b k) ≫ pullback.snd b k) (by
      rw [Category.assoc, hw, ← Category.assoc, pullback.condition,
        Category.assoc, pullback.condition, ← Category.assoc])

lemma persistence_centre_projection_deck
    {X Y B' B K : Over (Spec ↧ℂ)}
    (β : X ⟶ B') (βprev : Y ⟶ B) (b : B' ⟶ B) (k : K ⟶ B)
    (w : X ⟶ Y) (hw : w ≫ βprev = β ≫ b)
    (dX : X ⟶ X) (dY : Y ⟶ Y) (hdX : dX ≫ β = β)
    (hdY : dY ≫ βprev = βprev) (hdw : dX ≫ w = w ≫ dY) :
    s2b_preimageDeck β (pullback.fst b k) dX hdX ≫
        persistenceCentreProjection β βprev b k w hw =
      persistenceCentreProjection β βprev b k w hw ≫
        s2b_preimageDeck βprev k dY hdY := by
  apply pullback.hom_ext
  · dsimp only [persistenceCentreProjection, s2b_preimageDeck,
      s2b_toCover, s2b_toExceptional]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    rw [hdw]
  · dsimp only [persistenceCentreProjection, s2b_preimageDeck,
      s2b_toCover, s2b_toExceptional]
    simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

lemma persistence_centre_projection_cohomology_deck
    (Kcoeff : Type) [CommRing Kcoeff]
    {X Y B' B K : Over (Spec ↧ℂ)}
    (β : X ⟶ B') (βprev : Y ⟶ B) (b : B' ⟶ B) (k : K ⟶ B)
    (w : X ⟶ Y) (hw : w ≫ βprev = β ≫ b)
    (dX : X ⟶ X) (dY : Y ⟶ Y) (hdX : dX ≫ β = β)
    (hdY : dY ≫ βprev = βprev) (hdw : dX ≫ w = w ≫ dY)
    (n : ℕ) (u : Cohomology Kcoeff (TopCat.of (ComplexPoint (s2b_preimage βprev k))) n) :
    cohomologyMap Kcoeff n (TopCat.ofHom (Point.continuousMap
      (s2b_preimageDeck β (pullback.fst b k) dX hdX)))
        (cohomologyMap Kcoeff n (TopCat.ofHom (Point.continuousMap
          (persistenceCentreProjection β βprev b k w hw))) u) =
      cohomologyMap Kcoeff n (TopCat.ofHom (Point.continuousMap
        (persistenceCentreProjection β βprev b k w hw)))
          (cohomologyMap Kcoeff n (TopCat.ofHom (Point.continuousMap
            (s2b_preimageDeck βprev k dY hdY))) u) := by
  have hh :
      TopCat.ofHom (Point.continuousMap (s2b_preimageDeck β (pullback.fst b k) dX hdX)) ≫
          TopCat.ofHom (Point.continuousMap (persistenceCentreProjection β βprev b k w hw)) =
        TopCat.ofHom (Point.continuousMap (persistenceCentreProjection β βprev b k w hw)) ≫
          TopCat.ofHom (Point.continuousMap (s2b_preimageDeck βprev k dY hdY)) := by
    apply TopCat.ext
    intro x
    change (x ≫ s2b_preimageDeck β (pullback.fst b k) dX hdX) ≫
        persistenceCentreProjection β βprev b k w hw =
      (x ≫ persistenceCentreProjection β βprev b k w hw) ≫ s2b_preimageDeck βprev k dY hdY
    rw [Category.assoc, persistence_centre_projection_deck β βprev b k w hw dX dY hdX hdY hdw,
      Category.assoc]
  have h := congrArg (cohomologyMap Kcoeff n) hh
  rw [cohomologyMap_comp, cohomologyMap_comp] at h
  exact LinearMap.congr_fun h u

end HodgeLean.Foundations.QuotientDuality
