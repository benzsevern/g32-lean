import HodgeConjecture.Mathlib.Topology.Category.TopPair

/-! # Actual topological pair maps detected on ambient spaces
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual maps of topological pairs are determined by their ambient maps, using the specified target embedding.
Source: Mathlib, Topology/Category/TopPair.lean, TopPair.Hom.w and TopPair.isEmbedding_map.
HC no distance; AV milestone no distance. -/
theorem properCycle_top_pair_hom_ext {X Y : TopPair.{0}} {f g : X ⟶ Y}
    (h : TopPair.Hom.fst f = TopPair.Hom.fst g) : f = g := by
  apply MorphismProperty.Arrow.Hom.ext
  · ext x
    apply Y.isEmbedding_map.injective
    calc
      Y.map (TopPair.Hom.snd f x) = TopPair.Hom.fst f (X.map x) :=
        ConcreteCategory.congr_hom (TopPair.Hom.w f) x
      _ = TopPair.Hom.fst g (X.map x) := ConcreteCategory.congr_hom h (X.map x)
      _ = Y.map (TopPair.Hom.snd g x) :=
        (ConcreteCategory.congr_hom (TopPair.Hom.w g) x).symm
  · exact h

end HodgeLean.Foundations.QuotientDuality
