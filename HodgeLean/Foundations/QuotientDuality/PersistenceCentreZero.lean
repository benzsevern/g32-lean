import HodgeLean.Foundations.QuotientDuality.PersistenceCentreSurjectivity
import HodgeLean.Foundations.QuotientDuality.PersistenceProperDominantPoints
import HodgeLean.Foundations.QuotientDuality.PersistenceSurjectiveZeroCohomology

/-! Degree-zero centre detection by the actual equivariant exceptional projection. -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open HodgeLean.Foundations.Program AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

lemma persistence_centre_degree_zero_vanishing
    {X Y B' B K : Over (Spec ↧ℂ)} [LocallyOfFiniteType X.hom]
    (β : X ⟶ B') (βprev : Y ⟶ B) (b : B' ⟶ B) (k : K ⟶ B)
    (w : X ⟶ Y) (hw : w ≫ βprev = β ≫ b)
    [IsProper w.left] [IsDominant w.left]
    (dX : X ⟶ X) (dY : Y ⟶ Y) (hdX : dX ≫ β = β)
    (hdY : dY ≫ βprev = βprev) (hdw : dX ≫ w = w ≫ dY)
    (ζ : ℂ)
    (hvan : ∀ v : Cohomology ℂ
      (TopCat.of (ComplexPoint (s2b_preimage β (pullback.fst b k)))) 0,
      s2b_preimageCohomologyDeck β (pullback.fst b k) dX hdX 0 v = ζ • v → v = 0)
    (v : Cohomology ℂ (TopCat.of (ComplexPoint (s2b_preimage βprev k))) 0)
    (hv : s2b_preimageCohomologyDeck βprev k dY hdY 0 v = ζ • v) : v = 0 := by
  let p := TopCat.ofHom (Point.continuousMap
    (persistenceCentreProjection β βprev b k w hw))
  have hinj := persistence_surjective_cohomology_zero_injective ℂ p
    (persistence_centre_projection_point_surjective β βprev b k w hw
      (persistence_proper_dominant_point_surjective w))
  apply hinj
  rw [map_zero]
  apply hvan
  change cohomologyMap ℂ 0 _ (cohomologyMap ℂ 0 p v) = ζ • cohomologyMap ℂ 0 p v
  rw [persistence_centre_projection_cohomology_deck ℂ β βprev b k w hw dX dY
    hdX hdY hdw]
  change cohomologyMap ℂ 0 p (s2b_preimageCohomologyDeck βprev k dY hdY 0 v) = _
  rw [hv, map_smul]

end HodgeLean.Foundations.QuotientDuality
