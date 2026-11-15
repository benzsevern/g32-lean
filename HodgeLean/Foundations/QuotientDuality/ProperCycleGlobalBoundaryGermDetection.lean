import HodgeLean.Foundations.QuotientDuality.ProperCycleBoundaryGermDetection

/-! # Original global supported class detection off a one-degree boundary
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular TopologicalSpace
open HodgeLean.Adapters
namespace HodgeLean.Foundations.QuotientDuality

/-- Actual global supported classes are detected by their literal local restrictions off a boundary vanishing in the same support degree.
Source: properCycle_relative_zero_of_off_boundary_local_restrictions; a3b4a_classLocal_restrict_univ_injective; a3b4a_classLocal_restriction_comp.
HC no distance; AV milestone no distance. -/
lemma properCycle_global_zero_of_off_boundary_local_restrictions
    (X : TopCat.{0}) [T2Space X] [∀ V : Opens X, ParacompactSpace V]
    (S B : Closeds X) (hBS : B ≤ S) (n : ℕ)
    (hboundary : IsZero (RelativeCohomology ℚ
      (neighborhoodSupportComplementPair (Set.univ : Set X) B) n))
    (hlow : ∀ j : ℕ, j < n → IsZero (supportRelativeCohomologySheaf X S j))
    (a : CohomologyWithSupport ℚ X S n)
    (hloc : ∀ x ∈ S, x ∉ B → ∃ W : Opens X, x ∈ W ∧
      relativeCohomologyMap ℚ n (a3b4_neighborhoodPairMap (W : Set X) (S : Set X)) a = 0) : a = 0 := by
  apply a3b4a_classLocal_restrict_univ_injective (S : Set X) n
  rw [map_zero]
  apply properCycle_relative_zero_of_off_boundary_local_restrictions X S B hBS n hboundary hlow
  intro x hxS hxB
  obtain ⟨W, hxW, hW⟩ := hloc x hxS hxB
  refine ⟨W, hxW, ?_⟩
  exact (a3b4a_classLocal_restriction_comp (S : Set X)
    (show (W : Set X) ⊆ Set.univ from Set.subset_univ _) n a).trans hW

end HodgeLean.Foundations.QuotientDuality
