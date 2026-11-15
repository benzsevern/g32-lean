import HodgeLean.Foundations.QuotientDuality.ProperCycleLocalTransport
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedPointValues

/-! # The actual pair map underlying open point excision
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicTopology.Singular TopologicalSpace
namespace HodgeLean.Foundations.QuotientDuality

/-- The original open point-excision comparison is induced by the literal subspace inclusion on point-complement pairs.
Source: properCycle_open_local_homology_iso; neighborhoodPointComplementRelativeHomologyIso.
HC no distance; AV milestone no distance. -/
lemma properCycle_open_local_homology_iso_map
    (X : TopCat.{0}) [T1Space X] (W : Opens X) (w : W) (n : ℕ) :
    (properCycle_open_local_homology_iso X W w n).hom.hom =
      relativeHomologyMap ℚ n (imagePointPairMap
        (TopPair.ofSubset (X := X) (W : Set X)).map Subtype.val_injective w) := by
  let e : pointComplementPair (M := W) w ≅
      neighborhoodPointComplementPair (W : Set X) w.val :=
    TopPair.isoOfSubset (Homeomorph.refl W) (by
      intro z
      change (z.val ≠ w.val) ↔ z ≠ w
      exact not_congr Subtype.val_injective.eq_iff)
  have he : e.hom ≫ neighborhoodPointComplementPairMap (W : Set X) w.val =
      imagePointPairMap (TopPair.ofSubset (X := X) (W : Set X)).map
        Subtype.val_injective w := by
    ext z : 2 <;> rfl
  change (relativeHomologyMap ℚ n (neighborhoodPointComplementPairMap (W : Set X) w.val)).comp
    (relativeHomologyMap ℚ n e.hom) = _
  rw [← relativeHomologyMap_comp, he]

end HodgeLean.Foundations.QuotientDuality
