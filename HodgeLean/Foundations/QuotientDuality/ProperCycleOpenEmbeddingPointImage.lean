import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingLocalHomology

/-! # Point excision at a specified image of an actual open embedding
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual open embedding induces a bijection on original point homology at its specified image point.
Source: properCycle_open_embedding_local_homology_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_embedding_point_image_bijective
    {X Y : TopCat.{0}} [T1Space Y] (f : X ⟶ Y) (hf : Topology.IsOpenEmbedding f)
    (x : X) (y : Y) (he : f x = y) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (TopPair.ofSubsetHom f (show Set.MapsTo f ({x} : Set X)ᶜ ({y} : Set Y)ᶜ from
        fun z hz h => hz (hf.injective (h.trans he.symm))))) := by
  subst y
  exact properCycle_open_embedding_local_homology_bijective f hf x n

end HodgeLean.Foundations.QuotientDuality
