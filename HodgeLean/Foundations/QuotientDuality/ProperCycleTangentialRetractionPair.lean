import HodgeLean.Foundations.QuotientDuality.ProperCycleTangentialRetractionHomotopy

/-! # Actual point-pair maps for tangential retraction coordinates
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual tangential retraction with unchanged normal coordinate gives a map of the original point-complement pairs.
Source: properCycle_tangential_retraction_homotopy_avoids_point.
HC no distance; AV milestone no distance. -/
def properCycle_tangential_retraction_point_pair
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (U : Set (E × Y)) (hU : (0, y) ∈ U)
    (r : C(U, E)) (hr : ∀ u : U, u.val.2 = y → r u = u.val.1) :
    pointComplementPair (⟨(0, y), hU⟩ : U) ⟶ pointComplementPair ((0 : E), y) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun u : U => (r u, u.val.2), r.continuous.prodMk
      (continuous_snd.comp continuous_subtype_val)⟩) (by
        intro u hu he
        have hh := properCycle_tangential_retraction_homotopy_avoids_point E Y y U hU r hr 0 u hu
        apply hh
        exact ((properCycle_tangential_retraction_homotopy E Y U r).map_zero_left u).trans he)

/-- The original inclusion of an actual point neighborhood maps its point-complement pair to the original ambient point pair.
Source: TopPair.ofSubsetHom; Subtype.ext.
HC no distance; AV milestone no distance. -/
def properCycle_product_neighborhood_point_pair
    (E : Type) [Zero E] [TopologicalSpace E] (Y : TopCat.{0}) (y : Y)
    (U : Set (E × Y)) (hU : (0, y) ∈ U) :
    pointComplementPair (⟨(0, y), hU⟩ : U) ⟶ pointComplementPair ((0 : E), y) :=
  TopPair.ofSubsetHom
    (TopCat.ofHom ⟨fun u : U => u.val, continuous_subtype_val⟩ : TopCat.of U ⟶ TopCat.of (E × Y))
    (by
      intro u hu he
      apply hu
      apply Subtype.ext
      exact he)

/-- Tangential interpolation gives an actual homotopy of the original point-complement pair maps.
Source: properCycle_tangential_retraction_homotopy; properCycle_tangential_retraction_homotopy_avoids_point.
HC no distance; AV milestone no distance. -/
def properCycle_tangential_retraction_pair_homotopy
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (Y : TopCat.{0}) (y : Y) (U : Set (E × Y)) (hU : (0, y) ∈ U)
    (r : C(U, E)) (hr : ∀ u : U, u.val.2 = y → r u = u.val.1) :
    TopPair.Homotopy (properCycle_tangential_retraction_point_pair E Y y U hU r hr)
      (properCycle_product_neighborhood_point_pair E Y y U hU) := by
  let H := properCycle_tangential_retraction_homotopy E Y U r
  exact
    { fst := H
      snd :=
        { toFun := fun tu => ⟨H (tu.1, tu.2.val),
            properCycle_tangential_retraction_homotopy_avoids_point E Y y U hU r hr
              tu.1 tu.2.val tu.2.property⟩
          continuous_toFun := by
            apply Continuous.subtype_mk
            change Continuous (fun tu : unitInterval ×
              ↥(({(⟨(0, y), hU⟩ : U)} : Set U)ᶜ) => H (tu.1, tu.2.val))
            fun_prop
          map_zero_left := fun u => Subtype.ext (H.map_zero_left u.val)
          map_one_left := fun u => Subtype.ext (H.map_one_left u.val) }
      w := rfl }

end HodgeLean.Foundations.QuotientDuality
