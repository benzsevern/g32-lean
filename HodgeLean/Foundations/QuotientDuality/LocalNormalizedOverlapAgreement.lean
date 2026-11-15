import HodgeLean.Foundations.QuotientDuality.LocalNormalizedOrientationRestriction
import HodgeLean.Foundations.QuotientDuality.LocalCoherentSmoothNormalization
import HodgeLean.Foundations.QuotientDuality.LocalDenseOrientationUniqueness
import HodgeLean.Foundations.AnalyticDivisorAlgebraic24Proofs
import Mathlib.AlgebraicGeometry.Noetherian

/-! Normalized orientations have identical restrictions to every integral common open. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open AlgebraicTopology.Singular HodgeLean.Foundations.Analytic
namespace HodgeLean.Foundations.QuotientDuality

theorem normalized_open_pullbacks_agree
    (S X Y : Over (Spec ↧ℂ)) [IsIntegral S.left]
    [LocallyOfFiniteType S.hom] [QuasiCompact S.hom] [IsSeparated S.hom]
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
    [T2Space (ComplexPoint S)] [T2Space (ComplexPoint X)] [T2Space (ComplexPoint Y)]
    (jX : S ⟶ X) [IsOpenImmersion jX.left] (jY : S ⟶ Y) [IsOpenImmersion jY.left]
    (d : ℕ)
    (oX : LocalRationalOrientation (TopCat.of (ComplexPoint X)) (2 * d))
    (oY : LocalRationalOrientation (TopCat.of (ComplexPoint Y)) (2 * d))
    (hnX : ∀ (x : ComplexPoint X) (F : OpenPartialHomeomorph (ComplexPoint X) (Fin d → ℂ))
      (hx : x ∈ F.source),
      (∀ i, (f4_analytification X).IsHolFun (fun y : F.source => F y i)) →
      oX.generator x = localClassOfChart d F x hx)
    (hnY : ∀ (x : ComplexPoint Y) (F : OpenPartialHomeomorph (ComplexPoint Y) (Fin d → ℂ))
      (hx : x ∈ F.source),
      (∀ i, (f4_analytification Y).IsHolFun (fun y : F.source => F y i)) →
      oY.generator x = localClassOfChart d F x hx) :
    ∀ s : ComplexPoint S,
      (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap jX))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points jX) (2 * d) oX).generator s =
      (openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap jY))
        (HodgeLean.Foundations.ComplexTopology.openImmersion_points jY) (2 * d) oY).generator s := by
  let pX := openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap jX))
    (HodgeLean.Foundations.ComplexTopology.openImmersion_points jX) (2 * d) oX
  let pY := openEmbeddingOrientationPullback (TopCat.ofHom (Point.continuousMap jY))
    (HodgeLean.Foundations.ComplexTopology.openImmersion_points jY) (2 * d) oY
  obtain ⟨I, _⟩ := normalize_coherent_orientation_on_smooth_locus S d pX
  letI := I
  letI : IsNoetherian S.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian S.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace S.hom }
  let U := S.hom.smoothLocus
  let A := openScheme S U
  let k := openInclusion S U
  letI : NoetherianSpace S.left := IsNoetherian.noetherianSpace
  obtain ⟨a, ha⟩ := S.hom.dense_smoothLocus_of_perfectField.nonempty
  letI : Nonempty U := ⟨⟨a, ha⟩⟩
  have hS := HodgeLean.Foundations.AnalyticDivisorAlgebraic24.gaga24_dense_overOpen S U
  apply coherent_orientation_generators_eq_of_dense (TopCat.of (ComplexPoint S)) (2 * d)
    pX pY (Point.overOpen U) hS
  intro s hs
  let z := asOpenPoint S U s hs
  have hz : Point.map k z = s :=
    congrArg Subtype.val ((openHomeomorph S U).apply_symm_apply ⟨s, hs⟩)
  have H := (normalized_orientation_restriction_smooth_calibration A S X d jX k oX hnX z).trans
    (normalized_orientation_restriction_smooth_calibration A S Y d jY k oY hnY z).symm
  change pX.generator (Point.map k z) = pY.generator (Point.map k z) at H
  rw [hz] at H
  exact H

#print axioms normalized_open_pullbacks_agree
end HodgeLean.Foundations.QuotientDuality
