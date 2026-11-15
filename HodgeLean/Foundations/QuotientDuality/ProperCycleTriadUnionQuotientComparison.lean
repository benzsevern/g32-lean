import HodgeLean.Foundations.QuotientDuality.ProperCycleOpenPairQuotient
import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexOpenExcision

/-! # The literal union-relative map in the original triad quotient coordinates
HC no distance; AV milestone no distance. -/
noncomputable section
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The actual triad-to-union relative map is the literal quotient refinement through the two specified original comparisons.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_subset_union_subcomplex_triad_projection; triadRelativeChainProjection_triadToUnionRelativeChainMap.
HC no distance; AV milestone no distance. -/
theorem properCycle_triad_union_quotient_comparison (X : TopCat.{0}) (U V : Set X) :
    (properCycle_subset_union_subcomplex_triad_iso X U V).hom ≫
        triadToUnionRelativeChainMap ℚ X U V =
      properCycle_subcomplex_quotient_map
        (sup_le (properCycle_subset_subcomplex_mono X
          (Set.subset_union_left : U ⊆ U ∪ V))
          (properCycle_subset_subcomplex_mono X
            (Set.subset_union_right : V ⊆ U ∪ V))) ≫
        (properCycle_subset_subcomplex_relative_iso X (U ∪ V)).hom := by
  apply (cancel_epi (cokernel.π (SSet.chainComplexMap
    (subsetSingularSubcomplex X U ⊔ subsetSingularSubcomplex X V).ι
      (ModuleCat.of ℚ ℚ)))).mp
  rw [← Category.assoc, properCycle_subset_union_subcomplex_triad_projection,
    triadRelativeChainProjection_triadToUnionRelativeChainMap,
    ← Category.assoc, properCycle_subcomplex_quotient_projection,
    properCycle_subset_subcomplex_relative_projection]

/-- The original open-triad homology isomorphism is the actual quotient refinement followed by the specified relative comparison.
Source: Hatcher, Algebraic Topology, section 2.2; properCycle_triad_union_quotient_comparison.
HC no distance; AV milestone no distance. -/
theorem properCycle_open_triad_union_quotient_homology_comparison
    (X : TopCat.{0}) (U V : Set X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ) :
    (properCycle_subset_union_quotient_homology_iso X U V hU hV n).hom =
      HomologicalComplex.homologyMap (properCycle_subcomplex_quotient_map
        (sup_le (properCycle_subset_subcomplex_mono X
          (Set.subset_union_left : U ⊆ U ∪ V))
          (properCycle_subset_subcomplex_mono X
            (Set.subset_union_right : V ⊆ U ∪ V)))) n ≫
        HomologicalComplex.homologyMap
          (properCycle_subset_subcomplex_relative_iso X (U ∪ V)).hom n := by
  change HomologicalComplex.homologyMap
    (properCycle_subset_union_subcomplex_triad_iso X U V).hom n ≫
      HomologicalComplex.homologyMap (triadToUnionRelativeChainMap ℚ X U V) n = _
  rw [← HomologicalComplex.homologyMap_comp, properCycle_triad_union_quotient_comparison,
    HomologicalComplex.homologyMap_comp]

end HodgeLean.Foundations.QuotientDuality
