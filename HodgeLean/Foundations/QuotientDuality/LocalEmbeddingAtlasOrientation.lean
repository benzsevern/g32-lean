import HodgeLean.Foundations.QuotientDuality.LocalOpenCoverOrientation

/-! Gluing compatible orientations from an atlas of open embeddings. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

theorem open_embedding_atlas_coherent_orientation
    (Y : TopCat.{0}) [T2Space Y] (n : ℕ) (I : Type) (X : I → TopCat.{0})
    (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsOpenEmbedding (f i))
    (o : ∀ i, LocalRationalOrientation (X i) n)
    (hcover : ∀ y : Y, ∃ i, ∃ x : X i, f i x = y)
    (hcompat : ∀ (i j : I) (x : X i) (z : X j), f i x = f j z →
      HEq (openEmbeddingOrientationFamily (f i) (hf i) n (o i) x)
        (openEmbeddingOrientationFamily (f j) (hf j) n (o j) z)) :
    Nonempty (LocalRationalOrientation Y n) := by
  classical
  have cover := hcover
  choose idx pt hpt using cover
  let g (y : Y) : orientationGroup Y n y :=
    Eq.recOn (motive := fun z _ => orientationGroup Y n z) (hpt y)
      (openEmbeddingOrientationFamily (f (idx y)) (hf (idx y)) n (o (idx y)) (pt y))
  have hg (i : I) (x : X i) : g (f i x) =
      openEmbeddingOrientationFamily (f i) (hf i) n (o i) x := by
    dsimp only [g]
    exact eq_of_heq ((eqRec_heq (φ := fun y : Y => orientationGroup Y n y) (hpt (f i x)) _).trans
      (hcompat (idx (f i x)) i (pt (f i x)) x (hpt (f i x))))
  refine ⟨{ generator := g, generates := ?_, vanishes := ?_, coherent := ?_ }⟩
  · intro y
    obtain ⟨i, x, rfl⟩ := hcover y
    rw [hg]
    let m := relativeHomologyMap ℚ n (imagePointPairMap (f i) (hf i).injective x)
    have H : (fun q : ℚ => m (q • (o i).generator x)) =
        (fun q : ℚ => q • openEmbeddingOrientationFamily (f i) (hf i) n (o i) x) := by
      funext q
      exact map_smul _ _ _
    change Function.Bijective (fun q : ℚ => q • openEmbeddingOrientationFamily (f i) (hf i) n (o i) x)
    rw [← H]
    exact (openEmbedding_point_homology_bijective (f i) (hf i) x n).comp ((o i).generates x)
  · intro y k hk
    obtain ⟨i, x, rfl⟩ := hcover y
    letI := (o i).vanishes x k hk
    exact (openEmbedding_point_homology_bijective (f i) (hf i) x k).surjective.subsingleton
  · intro y
    obtain ⟨i, x, rfl⟩ := hcover y
    obtain ⟨V, hxV, c, hc⟩ := openEmbeddingOrientationFamily_locally_represented
      (f i) (hf i) n (o i) x
    let W : Opens Y := V ⊓ ⟨Set.range (f i), (hf i).isOpen_range⟩
    refine ⟨W, ⟨hxV, ⟨x, rfl⟩⟩,
      relativeHomologyMap ℚ n (supportInclusionPairMap Y (inf_le_left : W ≤ V)) c, ?_⟩
    intro z hz
    obtain ⟨a, rfl⟩ := hz.2
    exact (support_restriction_trans Y (Set.singleton_subset_iff.mpr hz)
      (inf_le_left : W ≤ V) n c).trans ((hc a hz.1).trans (hg i a).symm)

#print axioms open_embedding_atlas_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
