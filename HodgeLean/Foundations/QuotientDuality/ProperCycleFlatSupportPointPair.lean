import HodgeLean.Foundations.QuotientDuality.ProperCycleFlatSupportEmbedding
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingPointImage

/-! # The literal tangential point map of the original support chart
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original flattened support chart gives its actual tangential point-pair map.
Source: properCycle_flat_support_chart_isOpenEmbedding; TopPair.ofSubsetHom.
HC no distance; AV milestone no distance. -/
def properCycle_flat_support_point_pair
    (X : TopCat.{0}) (S : Set X) {E Y : Type} [TopologicalSpace E] [Zero E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (y : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hz : z.val ∈ e.source) (hcenter : (e z.val).1 = 0) :
    pointComplementPair (⟨z, hz⟩ : {s : S | s.val ∈ e.source}) ⟶ pointComplementPair (M := TopCat.of E) 0 := by
  let f : TopCat.of {s : S | s.val ∈ e.source} ⟶ TopCat.of E :=
    TopCat.ofHom ⟨fun s => (e s.val.val).1,
      (properCycle_flat_support_chart_isOpenEmbedding X S e y hflat).continuous⟩
  exact TopPair.ofSubsetHom f (by
    intro s hs he
    apply hs
    apply (properCycle_flat_support_chart_isOpenEmbedding X S e y hflat).injective
    exact he.trans hcenter.symm)

/-- The actual tangential support point map induces a bijection on local homology in every degree.
Source: properCycle_flat_support_chart_isOpenEmbedding; properCycle_open_embedding_local_homology_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_flat_support_point_pair_bijective
    (X : TopCat.{0}) (S : Set X) {E Y : Type} [TopologicalSpace E] [T1Space E]
    [Zero E] [TopologicalSpace Y]
    (e : OpenPartialHomeomorph X (E × Y)) (y : Y)
    (hflat : ∀ x ∈ e.source, x ∈ S ↔ (e x).2 = y)
    (z : S) (hz : z.val ∈ e.source) (hcenter : (e z.val).1 = 0) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (properCycle_flat_support_point_pair X S e y hflat z hz hcenter)) := by
  let f : TopCat.of {s : S | s.val ∈ e.source} ⟶ TopCat.of E :=
    TopCat.ofHom ⟨fun s => (e s.val.val).1,
      (properCycle_flat_support_chart_isOpenEmbedding X S e y hflat).continuous⟩
  exact properCycle_open_embedding_point_image_bijective f
    (properCycle_flat_support_chart_isOpenEmbedding X S e y hflat) ⟨z, hz⟩ 0 hcenter n

end HodgeLean.Foundations.QuotientDuality
