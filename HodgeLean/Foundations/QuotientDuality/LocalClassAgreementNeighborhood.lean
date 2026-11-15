import HodgeLean.Foundations.QuotientDuality.LocalHomologyNeighborhood

/-! Agreement of supported classes near a point where their local values agree. -/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory TopologicalSpace AlgebraicTopology.Singular
open HodgeLean.RealDefs
namespace HodgeLean.Foundations.QuotientDuality

theorem support_restriction_trans (X : TopCat.{0}) {Z W U : Set X}
    (hZW : Z ⊆ W) (hWU : W ⊆ U) (n : ℕ)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) Uᶜ) n) :
    relativeHomologyMap ℚ n (supportInclusionPairMap X hZW)
      (relativeHomologyMap ℚ n (supportInclusionPairMap X hWU) c) =
      relativeHomologyMap ℚ n (supportInclusionPairMap X (hZW.trans hWU)) c := by
  rw [← LinearMap.comp_apply, ← relativeHomologyMap_comp]
  rfl

theorem supported_classes_agree_near_point
    (X : TopCat.{0}) [T2Space X] (n : ℕ) (U V : Opens X) (x : X)
    (hxU : x ∈ U) (hxV : x ∈ V)
    (c : RelativeHomology ℚ (TopPair.ofSubset (X := X) (U : Set X)ᶜ) n)
    (d : RelativeHomology ℚ (TopPair.ofSubset (X := X) (V : Set X)ᶜ) n)
    (heq : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hxU)) c =
        relativeHomologyMap ℚ n
          (supportInclusionPairMap X (Set.singleton_subset_iff.mpr hxV)) d) :
    ∃ (W : Opens X) (hxW : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V),
      relativeHomologyMap ℚ n (supportInclusionPairMap X hWU) c =
        relativeHomologyMap ℚ n (supportInclusionPairMap X hWV) d := by
  let Z := U ⊓ V
  let cZ := relativeHomologyMap ℚ n (supportInclusionPairMap X (inf_le_left : Z ≤ U)) c
  let dZ := relativeHomologyMap ℚ n (supportInclusionPairMap X (inf_le_right : Z ≤ V)) d
  have hz : relativeHomologyMap ℚ n
      (supportInclusionPairMap X (Set.singleton_subset_iff.mpr (show x ∈ Z from ⟨hxU, hxV⟩)))
      (cZ - dZ) = 0 := by
    rw [map_sub]
    dsimp [cZ, dZ]
    erw [support_restriction_trans X (Set.singleton_subset_iff.mpr (show x ∈ Z from ⟨hxU, hxV⟩)) (inf_le_left : Z ≤ U) n c,
      support_restriction_trans X (Set.singleton_subset_iff.mpr (show x ∈ Z from ⟨hxU, hxV⟩)) (inf_le_right : Z ≤ V) n d, heq, sub_self]
  obtain ⟨W, hxW, hWZ, hzero⟩ := relative_class_zero_on_neighborhood X n Z x ⟨hxU, hxV⟩ (cZ - dZ) hz
  rw [map_sub] at hzero
  dsimp [cZ, dZ] at hzero
  erw [support_restriction_trans X hWZ (inf_le_left : Z ≤ U) n c,
    support_restriction_trans X hWZ (inf_le_right : Z ≤ V) n d, sub_eq_zero] at hzero
  exact ⟨W, hxW, hWZ.trans inf_le_left, hWZ.trans inf_le_right, hzero⟩

#print axioms supported_classes_agree_near_point
end HodgeLean.Foundations.QuotientDuality
