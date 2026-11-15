import HodgeLean.Foundations.BundleResolution.ChernRelativeDomainSequenceHelpers

/-! # Actual relative domain sequence augmentation

The actual small-chain comparison carries the two relative domain maps
to their original ambient pair inclusions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom
namespace HodgeLean.Foundations.BundleResolution

theorem i1_relativeDomainBinarySequence_g_augmentation (X : TopCat.{0}) (Z U V : Set X) :
    (i1_relativeDomainBinarySequence X Z U V).g ≫
        i1_relativeSmallChainComparison X Z (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V) =
      biprod.desc
        ((relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z U))
        ((relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z V)) := by
  change biprod.map (i1_subsetRelativeChainIso X Z U).hom (i1_subsetRelativeChainIso X Z V).hom ≫
    biprod.desc _ _ ≫ _ = _
  apply biprod.hom_ext'
  · simp only [biprod.inl_map_assoc, biprod.inl_desc_assoc, Category.assoc, biprod.inl_desc]
    exact (congrArg (fun q => (i1_subsetRelativeChainIso X Z U).hom ≫ q)
      (i1_relativeSmallChainComparison_naturality X Z (i1_singularSubsetRange X U)
        (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V) le_sup_left)).trans
          (i1_subsetRelativeChainIso_hom_comp X Z U)
  · simp only [biprod.inr_map_assoc, biprod.inr_desc_assoc, Category.assoc, biprod.inr_desc]
    exact (congrArg (fun q => (i1_subsetRelativeChainIso X Z V).hom ≫ q)
      (i1_relativeSmallChainComparison_naturality X Z (i1_singularSubsetRange X V)
        (i1_singularSubsetRange X U ⊔ i1_singularSubsetRange X V) le_sup_right)).trans
          (i1_subsetRelativeChainIso_hom_comp X Z V)

end HodgeLean.Foundations.BundleResolution
