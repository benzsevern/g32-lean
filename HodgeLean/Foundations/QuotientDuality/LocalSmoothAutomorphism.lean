import HodgeLean.Foundations.QuotientDuality.LocalSmoothUniqueness
import HodgeLean.RealDefs.Port.AlgebraicGeometry.ComplexPoint.CoclassSchemeIso

/-! Actual algebraic automorphisms fix the smooth complex fundamental class. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem smooth_projective_fundamental_iso_invariant
    (X : Over (Spec ↧ℂ)) [IsIntegral X.left] [Smooth X.hom] [IsProjective X.hom]
    (d : ℕ) [SmoothOfRelativeDimension d X.hom]
    (c : Homology ℚ (TopCat.of (ComplexPoint X)) (2 * d))
    (hc : ∀ x, localOrientation (TopCat.of (ComplexPoint X)) (2 * d) c x =
      complexLocalOrientation X d x) (e : X ≅ X) :
    homologyMap ℚ (2 * d) (TopCat.ofHom (Point.continuousMap e.hom)) c = c := by
  let H := Point.isoMapHomeomorph e
  apply compact_complex_charted_top_class_ext (TopCat.of (ComplexPoint X)) d
  intro y
  obtain ⟨x, rfl⟩ := H.surjective y
  have hn := localOrientation_map
    (X := TopCat.of (ComplexPoint X)) (Y := TopCat.of (ComplexPoint X)) (2 * d) x (H x) (pointComplementHomeomorphPairMap H x) c
  have hp : relativeHomologyMap ℚ (2 * d) (pointComplementHomeomorphPairMap H x)
      (complexLocalOrientation X d x) = complexLocalOrientation X d (H x) :=
    complexSchemeIsoPointPairMap_localClass X X e d x
  exact hn.symm.trans ((congrArg (relativeHomologyMap ℚ (2 * d)
    (pointComplementHomeomorphPairMap H x)) (hc x)).trans (hp.trans (hc (H x)).symm))

#print axioms smooth_projective_fundamental_iso_invariant
end HodgeLean.Foundations.QuotientDuality
