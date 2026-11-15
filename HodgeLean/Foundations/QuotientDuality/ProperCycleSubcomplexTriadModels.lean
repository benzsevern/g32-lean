import HodgeLean.Foundations.QuotientDuality.ProperCycleSubcomplexMVCapConnecting

/-! # Original relative and triad quotients under singular subcomplex comparison -/

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory CategoryTheory.Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.QuotientDuality

/-- The original singular-set image isomorphism retains the literal ambient chain inclusion.
Source: Hatcher, Algebraic Topology, section 2.1, singular chains of subspaces.
HC no distance; AV milestone no distance. -/
lemma properCycle_subset_singular_chain_iso_inclusion
    (X : TopCat.{0}) (T : Set X) :
    SSet.chainComplexMap (subsetSingularIso X T).hom (ModuleCat.of ℚ ℚ) ≫
        SSet.chainComplexMap (subsetSingularSubcomplex X T).ι (ModuleCat.of ℚ ℚ) =
      ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) T)).hom := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  change C.map _ ≫ C.map _ = C.map _
  rw [← C.map_comp]
  congr 1

/-- The quotient by the actual singular image subcomplex is the original relative chain complex of the subspace.
Source: Hatcher, Algebraic Topology, section 2.1, relative chains of subspaces.
HC no distance; AV milestone no distance. -/
def properCycle_subset_subcomplex_relative_iso
    (X : TopCat.{0}) (T : Set X) :
    properCycle_subcomplex_quotient (subsetSingularSubcomplex X T) ≅
      (relativeChainFunctor ℚ).obj (TopPair.ofSubset (X := X) T) := by
  let C := (SSet.chainComplexFunctor (ModuleCat ℚ)).obj (ModuleCat.of ℚ ℚ)
  let f := C.map (subsetSingularIso X T).hom
  let g := C.map (subsetSingularSubcomplex X T).ι
  letI : Epi f := by
    dsimp [f]
    infer_instance
  exact (cokernelEpiComp f g).symm ≪≫
    cokernelIsoOfEq (properCycle_subset_singular_chain_iso_inclusion X T)

/-- The original relative quotient comparison retains the literal ambient projection.
Source: Hatcher, Algebraic Topology, section 2.1, relative chain projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subset_subcomplex_relative_projection
    (X : TopCat.{0}) (T : Set X) :
    cokernel.π (SSet.chainComplexMap (subsetSingularSubcomplex X T).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_subset_subcomplex_relative_iso X T).hom =
      relativeChainProjection ℚ (TopPair.ofSubset (X := X) T) := by
  simp [properCycle_subset_subcomplex_relative_iso, cokernelEpiComp, relativeChainProjection]

/-- The quotient by the union of the actual singular image subcomplexes is the original sum-relative triad complex.
Source: Hatcher, Algebraic Topology, section 2.2, small-chain quotients and triads.
HC no distance; AV milestone no distance. -/
def properCycle_subset_union_subcomplex_triad_iso
    (X : TopCat.{0}) (A T : Set X) :
    properCycle_subcomplex_quotient (subsetSingularSubcomplex X A ⊔ subsetSingularSubcomplex X T) ≅
      triadRelativeChainComplex ℚ X A T := by
  letI : Epi (singularMayerVietorisShortComplex X A T).g :=
    (singularMayerVietorisShortComplex_shortExact X A T).epi_g
  exact (cokernelEpiComp (singularMayerVietorisShortComplex X A T).g
    (twoSubsetSmallChainInclusion X A T)).symm ≪≫
      cokernelIsoOfEq (singularMayerVietorisSumChainMap_eq X A T)

/-- The original triad comparison retains the literal ambient projection.
Source: Hatcher, Algebraic Topology, sections 2.1 and 2.2, sum-relative projections.
HC no distance; AV milestone no distance. -/
lemma properCycle_subset_union_subcomplex_triad_projection
    (X : TopCat.{0}) (A T : Set X) :
    cokernel.π (SSet.chainComplexMap
        (subsetSingularSubcomplex X A ⊔ subsetSingularSubcomplex X T).ι (ModuleCat.of ℚ ℚ)) ≫
        (properCycle_subset_union_subcomplex_triad_iso X A T).hom =
      triadRelativeChainProjection ℚ X A T := by
  simp [properCycle_subset_union_subcomplex_triad_iso, cokernelEpiComp,
    triadRelativeChainProjection, twoSubsetSmallChainInclusion]

end HodgeLean.Foundations.QuotientDuality
