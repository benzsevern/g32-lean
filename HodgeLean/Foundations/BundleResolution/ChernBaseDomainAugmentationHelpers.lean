import HodgeLean.Foundations.Singular.MayerVietoris

/-! # Actual ordinary binary domain sequence augmentation

The ordinary small-chain inclusion carries the two cover maps to the
original actual base-domain inclusions.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_baseDomainBinarySequence_g_augmentation (Y : TopCat.{0}) (U V : Set Y) :
    (singularMayerVietorisShortComplex Y U V).g ≫ twoSubsetSmallChainInclusion Y U V =
      biprod.desc (singularChainComplexMap ℚ (topologicalSubsetInclusion Y U))
        (singularChainComplexMap ℚ (topologicalSubsetInclusion Y V)) := by
  change biprod.desc
    (SSet.chainComplexMap (subsetLeftToSmallSingularSet Y U V) (ModuleCat.of ℚ ℚ))
    (SSet.chainComplexMap (subsetRightToSmallSingularSet Y U V) (ModuleCat.of ℚ ℚ)) ≫ _ = _
  apply biprod.hom_ext'
  · simp only [biprod.inl_desc_assoc, biprod.inl_desc]
    change SSet.chainComplexMap (subsetLeftToSmallSingularSet Y U V) (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap (subsetSingularSubcomplex Y U ⊔ subsetSingularSubcomplex Y V).ι
        (ModuleCat.of ℚ ℚ) = _
    rw [← Functor.map_comp]
    congr 1
  · simp only [biprod.inr_desc_assoc, biprod.inr_desc]
    change SSet.chainComplexMap (subsetRightToSmallSingularSet Y U V) (ModuleCat.of ℚ ℚ) ≫
      SSet.chainComplexMap (subsetSingularSubcomplex Y U ⊔ subsetSingularSubcomplex Y V).ι
        (ModuleCat.of ℚ ℚ) = _
    rw [← Functor.map_comp]
    congr 1

end HodgeLean.Foundations.BundleResolution
