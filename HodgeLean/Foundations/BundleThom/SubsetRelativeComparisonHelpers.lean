import HodgeLean.Foundations.BundleThom.SubsetRelativeChainIsoHelpers

/-! # Compatibility of actual relative-domain coordinates with ambient restriction

The domain range identifications preserve the actual ambient pair map before taking coclass pullbacks.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory Limits AlgebraicTopology AlgebraicTopology.Singular
namespace HodgeLean.Foundations.BundleThom

variable (X : TopCat) (Z U : Set X)
private local instance (T : TopCat) (S : Set T) : Mono (topologicalSubsetInclusion T S) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective
private local instance (T : TopCat) (S : Set T) :
    Mono (TopCat.toSSet.map (topologicalSubsetInclusion T S)) := by apply Functor.map_mono

/-- The actual domain chain-arrow isomorphism followed by small comparison is the supplied ambient pair map.
Source: Hatcher, Algebraic Topology, §2.2, naturality of subspace chain identifications. -/
theorem i1_subsetRelativeChainArrowIso_hom_comp :
    (i1_subsetRelativeChainArrowIso X Z U).hom ≫
      i1_relativeSmallChainArrowComparison X Z (i1_singularSubsetRange X U) =
        (chainPairFunctor ℚ).map (i1_subsetRelativePairInclusion X Z U) := by
  haveI : Mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)).hom := by
    change Mono (SSet.chainComplexMap
      (TopCat.toSSet.map (topologicalSubsetInclusion X Z)) (ModuleCat.of ℚ ℚ))
    dsimp [SSet.chainComplexMap, SSet.chainComplexFunctor]
    apply +allowSynthFailures Functor.map_mono
  have hr : ((i1_subsetRelativeChainArrowIso X Z U).hom ≫
      i1_relativeSmallChainArrowComparison X Z (i1_singularSubsetRange X U)).right =
      ((chainPairFunctor ℚ).map (i1_subsetRelativePairInclusion X Z U)).right := by
    change SSet.chainComplexMap
      (SSet.Subcomplex.toRange (TopCat.toSSet.map (topologicalSubsetInclusion X U))) (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap (i1_singularSubsetRange X U).ι (ModuleCat.of ℚ ℚ) =
        SSet.chainComplexMap (TopCat.toSSet.map (topologicalSubsetInclusion X U)) (ModuleCat.of ℚ ℚ)
    rw [← CategoryTheory.Functor.map_comp]
    dsimp only [i1_singularSubsetRange]
    rw [SSet.Subcomplex.toRange_ι]
  apply Arrow.hom_ext
  · apply (cancel_mono ((chainPairFunctor ℚ).obj (TopPair.ofSubset (X := X) Z)).hom).mp
    rw [Arrow.w, Arrow.w, hr]
  · exact hr

/-- The actual relative domain chain isomorphism preserves the supplied ambient relative chain map.
Source: Hatcher, Algebraic Topology, §2.2, naturality of relative chain identifications. -/
theorem i1_subsetRelativeChainIso_hom_comp :
    (i1_subsetRelativeChainIso X Z U).hom ≫
      i1_relativeSmallChainComparison X Z (i1_singularSubsetRange X U) =
        (relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z U) := by
  change (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ ≫
    (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _ =
      (coker (C := ChainComplex (ModuleCat ℚ) ℕ)).map _
  rw [← CategoryTheory.Functor.map_comp, i1_subsetRelativeChainArrowIso_hom_comp]

/-- Transport of actual ambient restriction agrees with the specified small-domain coclass restriction.
Source: Hatcher, Algebraic Topology, §3.1, naturality of rational relative coclasses. -/
theorem i1_subsetRelativeCoclassEquiv_restriction (n : ℕ)
    (u : RelativeCohomology ℚ (TopPair.ofSubset (X := X) Z) n) :
    i1_subsetRelativeCoclassEquiv X Z U n
      (relativeCohomologyMap ℚ n (i1_subsetRelativePairInclusion X Z U) u) =
      i1_chainDualPullback n (i1_relativeSmallChainComparison X Z (i1_singularSubsetRange X U)) u := by
  have hf : (i1_subsetRelativeChainIso X Z U).inv ≫
      (relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z U) =
        i1_relativeSmallChainComparison X Z (i1_singularSubsetRange X U) := by
    rw [← i1_subsetRelativeChainIso_hom_comp, Iso.inv_hom_id_assoc]
  change i1_chainDualPullback n (i1_subsetRelativeChainIso X Z U).inv
    (i1_chainDualPullback n ((relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z U)) u) = _
  rw [← LinearMap.comp_apply, ← i1_chainDualPullback_comp, hf]

end HodgeLean.Foundations.BundleThom
