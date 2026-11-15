import HodgeLean.Foundations.QuotientDuality.LocalClassAgreementNeighborhood
import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingOrientationFamily
import HodgeLean.Foundations.QuotientDuality.LocalOpenEmbeddingPointHomology

/-! Compatible coherent orientations on an open cover give a global orientation. -/
noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Topology TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

def openSubsetInclusion (X : TopCat.{0}) (U : Opens X) : TopCat.of U ⟶ X :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

theorem openSubsetInclusion_isOpenEmbedding (X : TopCat.{0}) (U : Opens X) :
    IsOpenEmbedding (openSubsetInclusion X U) := U.isOpen.isOpenEmbedding_subtypeVal

theorem open_cover_coherent_orientation
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (I : Type) (U : I → Opens X)
    (o : ∀ i, LocalRationalOrientation (TopCat.of (U i)) n)
    (hcover : ∀ x : X, ∃ i, x ∈ U i)
    (hcompat : ∀ (i j : I) (x : X) (hi : x ∈ U i) (hj : x ∈ U j),
      openEmbeddingOrientationFamily (openSubsetInclusion X (U i))
        (openSubsetInclusion_isOpenEmbedding X (U i)) n (o i) ⟨x, hi⟩ =
      openEmbeddingOrientationFamily (openSubsetInclusion X (U j))
        (openSubsetInclusion_isOpenEmbedding X (U j)) n (o j) ⟨x, hj⟩) :
    Nonempty (LocalRationalOrientation X n) := by
  classical
  choose idx hidx using hcover
  let g (x : X) := openEmbeddingOrientationFamily (openSubsetInclusion X (U (idx x)))
    (openSubsetInclusion_isOpenEmbedding X (U (idx x))) n (o (idx x)) ⟨x, hidx x⟩
  have hg (i : I) (x : X) (hx : x ∈ U i) :
      openEmbeddingOrientationFamily (openSubsetInclusion X (U i))
        (openSubsetInclusion_isOpenEmbedding X (U i)) n (o i) ⟨x, hx⟩ = g x :=
    hcompat i (idx x) x hx (hidx x)
  refine ⟨{ generator := g, generates := ?_, vanishes := ?_, coherent := ?_ }⟩
  · intro x
    let i := idx x
    let a : U i := ⟨x, hidx x⟩
    let f := openSubsetInclusion X (U i)
    let hf := openSubsetInclusion_isOpenEmbedding X (U i)
    have H : (fun q : ℚ => relativeHomologyMap ℚ n (imagePointPairMap f hf.injective a)
        (q • (o i).generator a)) = (fun q : ℚ => q • g x) := by
      funext q
      exact map_smul _ _ _
    change Function.Bijective (fun q : ℚ => q • g x)
    rw [← H]
    exact (openEmbedding_point_homology_bijective f hf a n).comp ((o i).generates a)
  · intro x k hk
    let i := idx x
    let a : U i := ⟨x, hidx x⟩
    letI := (o i).vanishes a k hk
    exact (openEmbedding_point_homology_bijective (openSubsetInclusion X (U i))
      (openSubsetInclusion_isOpenEmbedding X (U i)) a k).surjective.subsingleton
  · intro x
    let i := idx x
    let a : U i := ⟨x, hidx x⟩
    obtain ⟨V, hxV, c, hc⟩ := openEmbeddingOrientationFamily_locally_represented
      (openSubsetInclusion X (U i)) (openSubsetInclusion_isOpenEmbedding X (U i)) n (o i) a
    refine ⟨V ⊓ U i, ⟨hxV, hidx x⟩,
      relativeHomologyMap ℚ n (supportInclusionPairMap X (inf_le_left : V ⊓ U i ≤ V)) c, ?_⟩
    intro y hy
    have H := support_restriction_trans X (Set.singleton_subset_iff.mpr hy)
      (inf_le_left : V ⊓ U i ≤ V) n c
    exact H.trans ((hc ⟨y, hy.2⟩ hy.1).trans (hg i y hy.2))

#print axioms open_cover_coherent_orientation
end HodgeLean.Foundations.QuotientDuality
