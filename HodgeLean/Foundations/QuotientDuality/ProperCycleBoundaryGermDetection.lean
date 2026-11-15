import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundaryRestrictionInjective
import HodgeLean.Adapters.NormalConeB4aClassDetection

/-! # Original supported germ detection across a single vanishing boundary degree
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace Opposite
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Vanishing of local restrictions off an actual boundary detects the original class using only its single boundary support degree and lower support sheaf vanishing.
Source: properCycle_boundary_restriction_injective; ccm5_relativeGerms_injective_of_lowerVanishing; supportRelativeCohomologyGerm_restrict; Bredon, Sheaf Theory, second edition, II.10 and V.9.
HC no distance; AV milestone no distance. -/
lemma properCycle_relative_zero_of_off_boundary_local_restrictions
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S B : Closeds X) (hBS : B ≤ S) (n : ℕ)
    (hboundary : IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) B) n))
    (hlow : ∀ j : ℕ, j < n → IsZero (supportRelativeCohomologySheaf X S j))
    (a : RelativeCohomology ℚ (neighborhoodSupportComplementPair (Set.univ : Set X) S) n)
    (hloc : ∀ x ∈ S, x ∉ B → ∃ W : Opens X, x ∈ W ∧
      relativeCohomologyMap ℚ n
        (neighborhoodSupportInclusionPairMap
          (show (W : Set X) ⊆ Set.univ from Set.subset_univ _) (S : Set X)) a = 0) : a = 0 := by
  let U := B.compl
  have hH (j : ℕ) (hj : j < n) : IsZero
      ((U.isOpenEmbedding.sheafPullback AddCommGrpCat).obj (supportRelativeCohomologySheaf X S j)) :=
    (U.isOpenEmbedding.sheafPullback AddCommGrpCat).map_isZero (hlow j hj)
  apply (properCycle_boundary_restriction_injective X S B hBS n hboundary)
  rw [map_zero]
  apply ccm5_relativeGerms_injective_of_lowerVanishing X S U n hH
  funext x
  dsimp only
  have hg := supportRelativeCohomologyGerm_restrict X (S : Set X) n
    (show U ≤ ⊤ from le_top) x.val x.property a
  refine hg.trans ?_
  have hz : supportRelativeCohomologyGerm X (S : Set X) n U x.val x.property 0 = 0 := by
    simp only [supportRelativeCohomologyGerm, map_zero]
  rw [hz]
  by_cases hxS : x.val ∈ S
  · obtain ⟨W, hxW, hW⟩ := hloc x.val hxS x.property
    rw [← supportRelativeCohomologyGerm_restrict X (S : Set X) n
      (show W ≤ ⊤ from le_top) x.val hxW]
    exact (congrArg (supportRelativeCohomologyGerm X (S : Set X) n W x.val hxW) hW).trans
      (by simp only [supportRelativeCohomologyGerm, map_zero])
  · exact supportRelativeCohomologyGerm_eq_zero_of_not_mem X (S : Set X) n S.isClosed
      ⊤ x.val (Set.mem_univ _) hxS a

end HodgeLean.Foundations.QuotientDuality
