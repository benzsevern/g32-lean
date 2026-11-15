import HodgeLean.Foundations.QuotientDuality.ProperCycleChartLocalScalar

/-! # Detection of original ordinary classes through compact manifold supports -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

/-- An original ordinary class is detected by its actual compact smooth-support point values when its original projection to that support is injective.
Source: j5c_compact_manifold; properCycle_open_embedding_support_homology_bijective; properCycle_image_projected_support_point_value.
HC no distance; AV milestone no distance. -/
theorem properCycle_compact_manifold_support_point_detection
    {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (X Y : TopCat.{0}) [T2Space X] [T2Space Y] [ChartedSpace E Y]
    (f : Y ⟶ X) (hf : Topology.IsOpenEmbedding f) (S : Set Y) (hS : IsCompact S)
    (n : ℕ) (hn : Module.finrank ℝ E = n)
    (hproj : Function.Injective (relativeHomologyProjection ℚ
      (TopPair.ofSubset (X := X) (f '' S)ᶜ) n).hom)
    (c : Homology ℚ X n) (hc : ∀ y ∈ S, localOrientation X n c (f y) = 0) : c = 0 := by
  have hFS : IsClosed (f '' S) := (hS.image f.hom.continuous).isClosed
  obtain ⟨b, hb⟩ := (properCycle_open_embedding_support_homology_bijective f hf S hFS n).surjective
    ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) (f '' S)ᶜ) n).hom c)
  have hp (y : Y) (hy : y ∈ S) : relativeHomologyMap ℚ n
      (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr hy)) b = 0 := by
    apply (properCycle_open_embedding_local_homology_bijective f hf y n).injective
    change relativeHomologyMap ℚ n (imagePointPairMap f hf.injective y)
      (relativeHomologyMap ℚ n (supportInclusionPairMap Y (Set.singleton_subset_iff.mpr hy)) b) =
      relativeHomologyMap ℚ n (imagePointPairMap f hf.injective y) 0
    rw [map_zero]
    exact (properCycle_image_projected_support_point_value f hf.injective S n c b hb y hy).trans (hc y hy)
  have hb0 : b = 0 := (j5c_compact_manifold (M := Y) (E := E) hn hS).2 b hp
  apply hproj
  rw [map_zero, ← hb, hb0, map_zero]

end HodgeLean.Foundations.QuotientDuality
