import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodFundamental
import HodgeLean.Foundations.QuotientDuality.ProperCycleProjectedPointValues

/-! # Original point values of the actual excised relative ambient class
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.QuotientDuality

/-- Restriction of the actual excised relative ambient class to a support point and its original ambient point map retains the specified original local orientation.
Source: properCycle_neighborhood_relative_fundamental_pushforward; properCycle_support_projection_point_value.
HC no distance; AV milestone no distance. -/
lemma properCycle_neighborhood_fundamental_point_value
    (X : TopCat.{0}) (S U : Set X) (hS : IsClosed S) (hU : IsOpen U) (hSU : S ⊆ U)
    (n : ℕ) (c : Homology ℚ X n) (u : U) (hu : u.val ∈ S) :
    relativeHomologyMap ℚ n
      (imagePointPairMap (TopPair.ofSubset (X := X) U).map Subtype.val_injective u)
      (relativeHomologyMap ℚ n
        (supportInclusionPairMap (TopCat.of U) (Set.singleton_subset_iff.mpr hu))
        (properCycle_neighborhood_relative_fundamental X S U hS hU hSU n c)) =
      localOrientation X n c u.val := by
  let f := b6m_subspacePairMap X U Sᶜ
  let i := (TopPair.ofSubset (X := X) U).map
  have hs : supportInclusionPairMap (TopCat.of U) (Set.singleton_subset_iff.mpr hu) ≫
      imagePointPairMap i Subtype.val_injective u =
      f ≫ supportInclusionPairMap X (Set.singleton_subset_iff.mpr hu) := by
    ext z : 2 <;> rfl
  have hh := congrArg (fun g => relativeHomologyMap ℚ n g
    (properCycle_neighborhood_relative_fundamental X S U hS hU hSU n c)) hs
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at hh
  dsimp only [f] at hh
  exact hh.trans ((congrArg
    (relativeHomologyMap ℚ n (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hu)))
    (properCycle_neighborhood_relative_fundamental_pushforward X S U hS hU hSU n c)).trans
      (properCycle_support_projection_point_value X S n c u.val hu))

end HodgeLean.Foundations.QuotientDuality
