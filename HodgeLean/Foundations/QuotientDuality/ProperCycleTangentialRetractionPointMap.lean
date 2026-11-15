import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialRetractionPair
import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingLocalHomology

/-! # Original ambient local homology under actual tangential interpolation
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual tangential retraction coordinates induce exactly the original neighborhood inclusion map on ambient point homology.
Source: properCycle_tangential_retraction_pair_homotopy; TopPair.Homotopy.relativeHomologyMap_apply_eq.
HC no distance; AV milestone no distance. -/
lemma properCycle_tangential_retraction_point_map_eq
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (U : Set (E × Y)) (hU : (0, y) ∈ U)
    (r : C(U, E)) (hr : ∀ u : U, u.val.2 = y → r u = u.val.1) (n : ℕ) :
    relativeHomologyMap ℚ n (properCycle_tangential_retraction_point_pair E Y y U hU r hr) =
      relativeHomologyMap ℚ n (properCycle_product_neighborhood_point_pair E Y y U hU) := by
  ext c
  exact (properCycle_tangential_retraction_pair_homotopy E Y y U hU r hr).relativeHomologyMap_apply_eq
    (R := ℚ) n c

/-- On an actual open point neighborhood, tangential retraction coordinates give a bijection on original ambient point homology in every degree.
Source: properCycle_tangential_retraction_point_map_eq; properCycle_open_embedding_local_homology_bijective.
HC no distance; AV milestone no distance. -/
lemma properCycle_tangential_retraction_point_map_bijective
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) [T1Space Y] (y : Y) (U : Set (E × Y))
    (hUo : IsOpen U) (hU : (0, y) ∈ U)
    (r : C(U, E)) (hr : ∀ u : U, u.val.2 = y → r u = u.val.1) (n : ℕ) :
    Function.Bijective (relativeHomologyMap ℚ n
      (properCycle_tangential_retraction_point_pair E Y y U hU r hr)) := by
  rw [properCycle_tangential_retraction_point_map_eq E Y y U hU r hr n]
  let i : TopCat.of U ⟶ TopCat.of (E × Y) := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩
  exact properCycle_open_embedding_local_homology_bijective i
    hUo.isOpenEmbedding_subtypeVal (⟨(0, y), hU⟩ : U) n

end HodgeLean.Foundations.QuotientDuality
