import HodgeLean.Foundations.QuotientDuality.ProperCycleProductSupportPointPair

/-! # Original product source excision in ordinary support coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original product triad excision is ordinary support excision followed by the specified actual point pair identification.
Source: properCycle_product_triad_local_homology_iso; properCycle_support_cap_source_iso.
HC no distance; AV milestone no distance. -/
theorem properCycle_product_source_excision
    (E F : Type) [TopologicalSpace E] [T1Space E] [Zero E]
    [TopologicalSpace F] [T1Space F] [Zero F] (n : ℕ) :
    properCycle_product_triad_local_homology_iso E F n =
      properCycle_support_cap_source_iso (TopCat.of (E × F))
        (Prod.snd ⁻¹' ({0} : Set F)) {z | z.1 = 0}
        (isClosed_singleton.preimage continuous_snd)
        (isClosed_singleton.preimage continuous_fst) n ≪≫
      (relativeHomologyFunctor ℚ n).mapIso (properCycle_product_support_point_pair_iso E F) := by
  apply Iso.ext
  dsimp only [properCycle_product_triad_local_homology_iso,
    properCycle_triad_local_homology_iso, properCycle_support_cap_source_iso,
    properCycle_product_support_point_pair_iso, Iso.trans_hom, Iso.symm_hom,
    asIso_hom, CategoryTheory.Functor.mapIso_hom]
  rw [properCycle_relative_chain_subset_eq _ _ _ (properCycle_product_puncture_union E F)]
  dsimp only [relativeHomologyFunctor, HomologicalComplex.homologyFunctor]
  simp only [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map]
  simp only [Category.assoc, ← HomologicalComplex.homologyMap_comp,
    ← CategoryTheory.Functor.map_comp, Iso.hom_inv_id, Iso.hom_inv_id_assoc, Category.id_comp,
    CategoryTheory.Functor.mapIso_hom]

  rfl

end HodgeLean.Foundations.QuotientDuality
