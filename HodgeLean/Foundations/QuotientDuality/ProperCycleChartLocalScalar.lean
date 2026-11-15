import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedPointValues
import HodgeLean.RealDefs.ComplexFundamentalClass
import HodgeLean.RealDefs.Port.AlgebraicTopology.LocalHomology.ChartNeighborhoodOrientation

/-! # Original top homology classes have locally constant chart coefficients -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- Every original ordinary top class is one fixed rational multiple of the original chart orientation on an actual neighborhood of any specified chart point.
Source: j5c_convex_restrict_bijective; j5c_hasClassAlong_of_isCompact; properCycle_open_embedding_support_homology_bijective.
HC no distance; AV milestone no distance. -/
theorem properCycle_chart_local_scalar
    (X : TopCat.{0}) [T2Space X] (d : ℕ)
    (e : OpenPartialHomeomorph X (Fin d → ℂ)) (c : Homology ℚ X (2*d))
    (x : X) (hx : x ∈ e.source) :
    ∃ W : Opens X, x ∈ W ∧ ∃ hW : (W : Set X) ⊆ e.source, ∃ q : ℚ,
      ∀ (y : X) (hy : y ∈ W),
        localOrientation X (2*d) c y = q • localClassOfChart d e y (hW hy) := by
  let E := Fin d → ℂ
  let f := chartOrientationEmbeddingMap d e x hx
  have hf : Topology.IsOpenEmbedding f :=
    (chartModelEmbedding d e x hx).isOpenEmbedding (chartModelEmbedding_source d e x hx)
  have hf0 : f 0 = x := chartModelEmbedding_zero d e x hx
  let K : Set E := Metric.closedBall 0 1
  have hK : IsCompact K := isCompact_closedBall (0 : E) 1
  have hK0 : (0 : E) ∈ K := by simp [K]
  have hFK : IsClosed (f '' K) := (hK.image f.hom.continuous).isClosed
  obtain ⟨b, hb⟩ := (properCycle_open_embedding_support_homology_bijective f hf K hFK (2*d)).surjective
    ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (f '' K)ᶜ) (2*d)).hom c)
  have hn : Module.finrank ℝ E = 2*d := by
    dsimp [E]
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  obtain ⟨g, hg⟩ := j5c_hasClassAlong_of_isCompact (M := E) (E := E) hn
    (translatedStandardComplexLocalClass d)
    (j5c_translatedStandardComplexLocalClass_locallyCoherent d) hK
  have hpoint (v : E) (hv : v ∈ K) :=
    properCycle_image_projected_support_point_value f hf.injective K (2*d) c b hb v hv
  have hgen (v : E) (hv : v ∈ K) : relativeHomologyMap ℚ (2*d)
      (imagePointPairMap f hf.injective v)
      (relativeHomologyMap ℚ (2*d)
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hv)) g) =
      localClassOfChart d e (f v) (chartOrientationEmbeddingMap_mem_source d e x hx v) := by
    rw [hg v hv]
    unfold translatedStandardComplexLocalClass
    rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
    exact chartOrientationEmbeddingMap_translate_standardComplexLocalClass d e x hx v
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp
    (show localOrientation X (2*d) c (f 0) ∈ Submodule.span ℚ
      {localClassOfChart d e (f 0) (chartOrientationEmbeddingMap_mem_source d e x hx 0)} by
      rw [span_localClassOfChart_eq_top]; trivial)
  have h0 : relativeHomologyMap ℚ (2*d)
      (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hK0)) b =
      q • relativeHomologyMap ℚ (2*d)
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hK0)) g := by
    apply (properCycle_open_embedding_local_homology_bijective f hf 0 (2*d)).injective
    change relativeHomologyMap ℚ (2*d) (imagePointPairMap f hf.injective 0)
      (relativeHomologyMap ℚ (2*d)
        (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hK0)) b) =
      relativeHomologyMap ℚ (2*d) (imagePointPairMap f hf.injective 0)
        (q • relativeHomologyMap ℚ (2*d)
          (supportInclusionPairMap (TopCat.of E) (Set.singleton_subset_iff.mpr hK0)) g)
    rw [map_smul, hpoint 0 hK0, hgen 0 hK0]
    exact hq.symm
  have hbg : b = q • g := by
    apply (j5c_convex_restrict_bijective (convex_closedBall (0 : E) 1) hK hK0 (2*d)).injective
    simpa only [map_smul] using h0
  have hvalue (v : E) (hv : v ∈ K) : localOrientation X (2*d) c (f v) =
      q • localClassOfChart d e (f v) (chartOrientationEmbeddingMap_mem_source d e x hx v) := by
    rw [← hpoint v hv, hbg, map_smul, map_smul, hgen v hv]
  let W : Opens X := ⟨f '' Metric.ball 0 1, hf.isOpenMap _ Metric.isOpen_ball⟩
  have hW : (W : Set X) ⊆ e.source := by
    rintro y ⟨v, _, rfl⟩
    exact chartOrientationEmbeddingMap_mem_source d e x hx v
  refine ⟨W, ⟨0, by simp, hf0⟩, hW, q, ?_⟩
  rintro y ⟨v, hv, rfl⟩
  exact hvalue v (Metric.ball_subset_closedBall hv)

end HodgeLean.Foundations.QuotientDuality
