import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cBallOrientation
import HodgeLean.Foundations.Program.HurwitzFamilyMarkedB62cComplexOrientation
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartNeighborhoodOrientation

noncomputable section
namespace HodgeLean.Foundations.Program
open CategoryTheory Topology AlgebraicTopology.Singular
variable (R : Type) [CommRing R] (d : ℕ)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_relativeHomologyMap_cast {P Q : TopPair} {m n : ℕ} (h : m = n)
    (f : P ⟶ Q) (c : RelativeHomology R P m) :
    relativeHomologyMap R n f (h ▸ c) = h ▸ relativeHomologyMap R m f c := by aesop

set_option backward.isDefEq.respectTransparency false in
def b6m_standardComplexOrientationNeighborhoodClass (d : ℕ) :
    RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of (Fin d → ℂ))
        (standardComplexOrientationNeighborhood d : Set (Fin d → ℂ))ᶜ) (2 * d) :=
  (Nat.mul_comm d 2) ▸
    relativeHomologyMap R (d * 2)
      (imageSupportPairMap (standardRealToComplexMap d) (standardRealToComplexMap_injective d)
        (standardOrientationBall (d * 2))) (b6m_standardOrientationBallClass R (d * 2))

set_option backward.isDefEq.respectTransparency false in
theorem b6m_standardComplexOrientationNeighborhoodClass_restrict (d : ℕ) (y : Fin d → ℂ)
    (hy : y ∈ standardComplexOrientationNeighborhood d) :
    relativeHomologyMap R (2 * d)
      (supportInclusionPairMap (TopCat.of (Fin d → ℂ)) (Set.singleton_subset_iff.mpr hy))
      (b6m_standardComplexOrientationNeighborhoodClass R d) =
      relativeHomologyMap R (2 * d) (translationPointComplementPairMap (Fin d → ℂ) y)
        (standardComplexLocalClass R d) := by
  obtain ⟨v, hv, rfl⟩ := hy
  rw [b6m_standardComplexOrientationNeighborhoodClass, b6m_relativeHomologyMap_cast R]
  change (Nat.mul_comm d 2) ▸ relativeHomologyMap R (d * 2) _
      (relativeHomologyMap R (d * 2) _ (b6m_standardOrientationBallClass R (d * 2))) = _
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    imageSupportPairMap_restrict _ _ _ _ hv,
    relativeHomologyMap_comp, LinearMap.comp_apply,
    show supportInclusionPairMap (TopCat.of (Fin (d * 2) → ℝ))
        (Set.singleton_subset_iff.mpr hv) = standardOrientationBallPointMap (d * 2) v hv from rfl,
    b6m_standardOrientationBallClass_restrict R, ← LinearMap.comp_apply,
    ← relativeHomologyMap_comp, standardRealToComplexPair_translation,
    relativeHomologyMap_comp, LinearMap.comp_apply]
  exact (b6m_relativeHomologyMap_cast R (Nat.mul_comm d 2) _ _).symm

variable {M : Type} [TopologicalSpace M]
variable (e : OpenPartialHomeomorph M (Fin d → ℂ)) (x : M) (hx : x ∈ e.source)

set_option backward.isDefEq.respectTransparency false in
def b6m_localClassOfChart : RelativeHomology R (pointComplementPair x) (2 * d) :=
  relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e x hx)
    (standardComplexLocalClass R d)

set_option backward.isDefEq.respectTransparency false in
lemma b6m_radialTargetPointPairMap_normalization
    (U : Set (Fin d → ℂ)) (c : Fin d → ℂ) (r : ℝ)
    (hr : 0 < r) (hball : Metric.ball c r ⊆ U) (v q : Fin d → ℂ)
    (hq : OpenPartialHomeomorph.univBall c r v = q) :
    relativeHomologyMap R (2 * d) (neighborhoodPointComplementPairMap U q)
      (relativeHomologyMap R (2 * d)
        (radialTargetPointPairMap d U c r hr hball v q hq) (standardComplexLocalClass R d)) =
      relativeHomologyMap R (2 * d) (translationPointComplementPairMap (Fin d → ℂ) q)
        (standardComplexLocalClass R d) := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp,
    radialTargetPointPairMap_comp_inclusion, relativeHomologyMap_comp, LinearMap.comp_apply,
    b6m_centeredUnivBall_preserves_localClass R d c r hr v]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_radialTargetPointPairMap_class_eq
    (U : Set (Fin d → ℂ)) (hU : IsOpen U)
    (c c' : Fin d → ℂ) (r r' : ℝ) (hr : 0 < r) (hr' : 0 < r')
    (hball : Metric.ball c r ⊆ U) (hball' : Metric.ball c' r' ⊆ U)
    (v v' q : Fin d → ℂ)
    (hq : OpenPartialHomeomorph.univBall c r v = q)
    (hq' : OpenPartialHomeomorph.univBall c' r' v' = q) :
    relativeHomologyMap R (2 * d)
      (radialTargetPointPairMap d U c r hr hball v q hq) (standardComplexLocalClass R d) =
      relativeHomologyMap R (2 * d)
        (radialTargetPointPairMap d U c' r' hr' hball' v' q hq')
          (standardComplexLocalClass R d) := by
  have hqU : q ∈ U := by
    rw [← hq]
    apply hball
    rw [← OpenPartialHomeomorph.univBall_target c hr]
    exact (OpenPartialHomeomorph.univBall c r).map_source (by simp)
  apply (b6m_point_excision_bijective R U q hU hqU (2 * d)).1
  rw [b6m_radialTargetPointPairMap_normalization R, b6m_radialTargetPointPairMap_normalization R]

set_option backward.isDefEq.respectTransparency false in
theorem b6m_chartOrientationEmbeddingMap_translate_standardComplexLocalClass (v : Fin d → ℂ) :
    relativeHomologyMap R (2 * d)
      (translationPointComplementPairMap (Fin d → ℂ) v ≫
        imagePointPairMap (chartOrientationEmbeddingMap d e x hx)
          (chartOrientationEmbeddingMap_injective d e x hx) v)
      (standardComplexLocalClass R d) =
      b6m_localClassOfChart R d e (chartOrientationEmbeddingMap d e x hx v)
        (chartOrientationEmbeddingMap_mem_source d e x hx v) := by
  let q := OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx) v
  have hq : q ∈ e.target := by
    apply ball_chartRadius_subset d e x hx
    rw [← OpenPartialHomeomorph.univBall_target (e x) (chartRadius_pos d e x hx)]
    exact (OpenPartialHomeomorph.univBall (e x) (chartRadius d e x hx)).map_source (by simp)
  let y := chartOrientationEmbeddingMap d e x hx v
  have hy : y ∈ e.source := chartOrientationEmbeddingMap_mem_source d e x hx v
  have hq' : OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) 0 = q := by
    rw [OpenPartialHomeomorph.univBall_apply_zero]
    exact chartOrientationEmbeddingMap_coordinates d e x hx v
  let P := radialTargetPointPairMap d e.target (e x) (chartRadius d e x hx)
    (chartRadius_pos d e x hx) (ball_chartRadius_subset d e x hx) v q rfl
  let Q := radialTargetPointPairMap d e.target (e y) (chartRadius d e y hy)
    (chartRadius_pos d e y hy) (ball_chartRadius_subset d e y hy) 0 q hq'
  let I := chartTargetInversePointPairMap d e q hq
  have hP : translationPointComplementPairMap (Fin d → ℂ) v ≫
      imagePointPairMap (chartOrientationEmbeddingMap d e x hx)
        (chartOrientationEmbeddingMap_injective d e x hx) v = P ≫ I := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w; apply Subtype.ext; rfl
    · ext w; rfl
  have hQ : chartModelEmbeddingPair d e y hy = Q ≫ I := by
    apply MorphismProperty.Arrow.Hom.ext
    · ext w
      apply Subtype.ext
      change e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) w.1) =
        e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) (w.1 + 0))
      rw [add_zero]
    · ext w
      have h (z : Fin d → ℂ) :
          e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) z) =
            e.symm (OpenPartialHomeomorph.univBall (e y) (chartRadius d e y hy) (z + 0)) := by
        rw [add_zero]
      exact h w
  have hclasses : relativeHomologyMap R (2 * d) P (standardComplexLocalClass R d) =
      relativeHomologyMap R (2 * d) Q (standardComplexLocalClass R d) :=
    b6m_radialTargetPointPairMap_class_eq R d e.target e.open_target
      (e x) (e y) (chartRadius d e x hx) (chartRadius d e y hy)
      (chartRadius_pos d e x hx) (chartRadius_pos d e y hy)
      (ball_chartRadius_subset d e x hx) (ball_chartRadius_subset d e y hy) v 0 q rfl hq'
  change relativeHomologyMap R (2 * d) _ (standardComplexLocalClass R d) =
    relativeHomologyMap R (2 * d) (chartModelEmbeddingPair d e y hy)
      (standardComplexLocalClass R d)
  rw [hP, hQ, relativeHomologyMap_comp, relativeHomologyMap_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, hclasses]

set_option backward.isDefEq.respectTransparency false in
def b6m_chartOrientationNeighborhoodClass :
    RelativeHomology R
      (TopPair.ofSubset (X := TopCat.of M) (chartOrientationNeighborhood d e x hx : Set M)ᶜ)
      (2 * d) :=
  relativeHomologyMap R (2 * d)
    (imageSupportPairMap (chartOrientationEmbeddingMap d e x hx)
      (chartOrientationEmbeddingMap_injective d e x hx) (standardComplexOrientationNeighborhood d))
    (b6m_standardComplexOrientationNeighborhoodClass R d)

set_option backward.isDefEq.respectTransparency false in
theorem b6m_chartOrientationNeighborhoodClass_restrict (y : M)
    (hy : y ∈ chartOrientationNeighborhood d e x hx) :
    relativeHomologyMap R (2 * d)
      (supportInclusionPairMap (TopCat.of M) (Set.singleton_subset_iff.mpr hy))
      (b6m_chartOrientationNeighborhoodClass R d e x hx) =
      b6m_localClassOfChart R d e y (chartOrientationNeighborhood_subset_source d e x hx hy) := by
  obtain ⟨v, hv, rfl⟩ := hy
  have hmap := congrArg (fun f => relativeHomologyMap R (2 * d) f
      (b6m_standardComplexOrientationNeighborhoodClass R d))
    (imageSupportPairMap_restrict (chartOrientationEmbeddingMap d e x hx)
      (chartOrientationEmbeddingMap_injective d e x hx)
      (standardComplexOrientationNeighborhood d) v hv)
  rw [relativeHomologyMap_comp, relativeHomologyMap_comp, LinearMap.comp_apply,
    LinearMap.comp_apply, b6m_standardComplexOrientationNeighborhoodClass_restrict R d v hv] at hmap
  calc
    _ = relativeHomologyMap R (2 * d)
        (imagePointPairMap (chartOrientationEmbeddingMap d e x hx)
          (chartOrientationEmbeddingMap_injective d e x hx) v)
        (relativeHomologyMap R (2 * d) (translationPointComplementPairMap (Fin d → ℂ) v)
          (standardComplexLocalClass R d)) := hmap
    _ = _ := by
      rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
      exact b6m_chartOrientationEmbeddingMap_translate_standardComplexLocalClass R d e x hx v

end HodgeLean.Foundations.Program
