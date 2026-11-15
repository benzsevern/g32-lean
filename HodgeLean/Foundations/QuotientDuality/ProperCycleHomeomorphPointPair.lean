import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingLocalHomology

/-! # Actual point-pair comparison for a homeomorphism with specified point image
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- An actual homeomorphism maps the original point pair to its specified point image.
Source: TopPair.ofSubsetHom; Homeomorph.injective.
HC no distance; AV milestone no distance. -/
def properCycle_homeomorph_point_pair
    (X Y : TopCat.{0}) (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) :
    pointComplementPair x ⟶ pointComplementPair y :=
  TopPair.ofSubsetHom (TopCat.ofHom ⟨e, e.continuous⟩ : X ⟶ Y) (by
    intro u hu hy
    apply hu
    apply e.injective
    exact hy.trans he.symm)

/-- The actual homeomorphism with its specified point image gives a bijection on original point homology in every degree.
Source: properCycle_open_embedding_local_homology_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_homeomorph_point_pair_bijective
    (X Y : TopCat.{0}) [T1Space Y] (e : X ≃ₜ Y) (x : X) (y : Y) (he : e x = y) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n (properCycle_homeomorph_point_pair X Y e x y he)) := by
  subst y
  exact properCycle_open_embedding_local_homology_bijective
    (TopCat.ofHom ⟨e, e.continuous⟩ : X ⟶ Y) e.isOpenEmbedding x n

end HodgeLean.Foundations.QuotientDuality
