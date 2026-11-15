import HodgeLean.Foundations.QuotientDuality.LocalNormalizedImmersionOrientation
import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingOrientationPullback
import HodgeLean.Foundations.QuotientDuality.LocalPointMapComposition

/-! Smooth calibration persists under restriction to an open subscheme. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem normalized_orientation_restriction_smooth_calibration
    (A S X : Over (Spec ↧ℂ)) (d : ℕ) [SmoothOfRelativeDimension d A.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [T2Space (ComplexPoint S)] [T2Space (ComplexPoint X)]
    (j : S ⟶ X) [IsOpenImmersion j.left] (k : A ⟶ S) [IsOpenImmersion k.left]
    (o : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (hn : ∀ (x : ComplexPoint X) (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
      (hx : x ∈ F.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i)) →
      o.generator x = localClassOfChart d F x hx)
    (z : ComplexPoint A) :
    (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap j))
      (HodgeLean.Foundations.ComplexTopology.openImmersion_points j) (2 * d) o).generator
        (Point.map k z) = immersionComplexOrientation A S d k z := by
  letI : IsOpenImmersion (k ≫ j).left :=
    inferInstanceAs (IsOpenImmersion (k.left ≫ j.left))
  let f := TopCat.ofHom (Point.continuousMap j)
  let hf := HodgeLean.Foundations.ComplexTopology.openImmersion_points j
  let g := TopCat.ofHom (Point.continuousMap k)
  let hg := HodgeLean.Foundations.ComplexTopology.openImmersion_points k
  apply (openEmbedding_point_homology_bijective f hf (Point.map k z) (2 * d)).injective
  have H := openEmbeddingOrientationPullback_generator f hf (2 * d) o (Point.map k z)
  refine H.trans ((normalized_orientation_on_smooth_immersion A X d (k ≫ j) o hn z).trans ?_)
  exact (point_homology_map_comp g f hg.injective hf.injective z (2 * d)
    (complexLocalOrientation A d z)).symm

#print axioms normalized_orientation_restriction_smooth_calibration
end HodgeLean.Foundations.QuotientDuality
