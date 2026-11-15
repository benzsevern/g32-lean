import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenEmbeddingSupportHomology
import HodgeLean.Foundations.QuotientDuality.ProperCycleNeighborhoodCapNaturality

/-! # Original point values of actual projected support classes -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The literal support restriction of the original projected class is its original local orientation value.
Source: properCycle_relative_homology_projection_naturality; homologyMap_id.
HC no distance; AV milestone no distance. -/
theorem properCycle_support_projection_point_value
    (X : TopCat.{0}) (S : Set X) (n : ℕ) (c : Homology ℚ X n) (x : X) (hx : x ∈ S) :
    relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))
      ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) Sᶜ) n).hom c) =
      localOrientation X n c x := by
  have h := properCycle_relative_homology_projection_naturality
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) n c
  change relativeHomologyMap ℚ n
    (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx))
    ((relativeHomologyProjection ℚ (TopPair.ofSubset (X := X) Sᶜ) n).hom c) =
      localOrientation X n (homologyMap ℚ n (𝟙 X) c) x at h
  rw [homologyMap_id, LinearMap.id_apply] at h
  exact h

/-- An actual source support class mapping to an original projected class retains its specified original point values under the literal point map.
Source: imageSupportPairMap_restrict; properCycle_support_projection_point_value.
HC no distance; AV milestone no distance. -/
theorem properCycle_image_projected_support_point_value
    {X Y : TopCat.{0}} (f : X ⟶ Y) (hf : Function.Injective f) (S : Set X) (n : ℕ)
    (c : Homology ℚ Y n) (b : RelativeHomology ℚ (TopPair.ofSubset (X := X) Sᶜ) n)
    (hb : relativeHomologyMap ℚ n (imageSupportPairMap f hf S) b =
      (relativeHomologyProjection ℚ (TopPair.ofSubset (X := Y) (f '' S)ᶜ) n).hom c)
    (x : X) (hx : x ∈ S) :
    relativeHomologyMap ℚ n (imagePointPairMap f hf x)
      (relativeHomologyMap ℚ n
        (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hx)) b) =
      localOrientation Y n c (f x) := by
  have h := congrArg (fun g => relativeHomologyMap ℚ n g b)
    (imageSupportPairMap_restrict f hf S x hx)
  simp only [relativeHomologyMap_comp, LinearMap.comp_apply] at h
  rw [hb] at h
  exact h.symm.trans (properCycle_support_projection_point_value Y (f '' S) n c (f x)
    (Set.mem_image_of_mem f hx))

end HodgeLean.Foundations.QuotientDuality
