import HodgeLean.Foundations.BundleResolution.ChernDomainCapBinarySequenceHelpers
import HodgeLean.Foundations.BundleResolution.ChernRelativeDomainAugmentationHelpers
import HodgeLean.Foundations.BundleResolution.ChernBaseDomainAugmentationHelpers
import HodgeLean.Foundations.BundleResolution.ChernGlobalDomainCapChainHelpers

/-! # Actual binary cap augmentation square

The induced small-chain union cap comparison agrees with global cap after
the actual relative and ordinary small-chain augmentation maps.
HC no distance; AV milestone no distance. -/

noncomputable section
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits HomologicalComplex AlgebraicTopology AlgebraicTopology.Singular
open HodgeLean.Foundations.BundleThom HodgeLean.Foundations.Singular
namespace HodgeLean.Foundations.BundleResolution

theorem i1_domainCapBinaryUnion_augmentation (X Y : TopCat.{0})
    (f : X ⟶ Y) (Z : Set X) (U V : Set Y) (k : ℕ)
    (φ : RelativeCocycle ℚ (TopPair.ofSubset (X := X) Z) (2 * k)) :
    HomologicalComplex.extendMap
        (i1_relativeSmallChainComparison X Z
          (i1_singularSubsetRange X (f ⁻¹' U) ⊔ i1_singularSubsetRange X (f ⁻¹' V)))
        (ComplexShape.embeddingUpIntLE (2 * k : ℕ)) ≫
      i1_globalEvenCapExtendedMap X Y f Z k φ =
    (i1_domainCapBinarySequenceComparison X Y f Z U V k φ).τ₃ ≫
      HomologicalComplex.extendMap (twoSubsetSmallChainInclusion Y U V)
        (ComplexShape.embeddingUpIntLE 0) := by
  let S := i1_relativeDomainBinarySequence X Z (f ⁻¹' U) (f ⁻¹' V)
  let T := singularMayerVietorisShortComplex Y U V
  let Fp := (ComplexShape.embeddingUpIntLE (2 * k : ℕ)).extendFunctor (ModuleCat.{0} ℚ)
  let F0 := (ComplexShape.embeddingUpIntLE 0).extendFunctor (ModuleCat.{0} ℚ)
  let r := (i1_domainCapBinarySequenceComparison X Y f Z U V k φ).τ₃
  let m := i1_extendedBinaryComparison (2 * k : ℕ)
    (i1_domainEvenCapExtendedMap X Y f Z U k φ) (i1_domainEvenCapExtendedMap X Y f Z V k φ)
  let asrc := i1_relativeSmallChainComparison X Z
    (i1_singularSubsetRange X (f ⁻¹' U) ⊔ i1_singularSubsetRange X (f ⁻¹' V))
  let atgt := twoSubsetSmallChainInclusion Y U V
  let ru := (relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z (f ⁻¹' U))
  let rv := (relativeChainFunctor ℚ).map (i1_subsetRelativePairInclusion X Z (f ⁻¹' V))
  let bu := singularChainComplexMap ℚ (topologicalSubsetInclusion Y U)
  let bv := singularChainComplexMap ℚ (topologicalSubsetInclusion Y V)
  have hs : Fp.map S.g ≫ Fp.map asrc = Fp.map (biprod.desc ru rv) := by
    rw [← Fp.map_comp]
    exact congrArg Fp.map (i1_relativeDomainBinarySequence_g_augmentation X Z (f ⁻¹' U) (f ⁻¹' V))
  have ht : F0.map T.g ≫ F0.map atgt = F0.map (biprod.desc bu bv) := by
    rw [← F0.map_comp]
    exact congrArg F0.map (i1_baseDomainBinarySequence_g_augmentation Y U V)
  have hc : Fp.map S.g ≫ r = m ≫ F0.map T.g :=
    (i1_domainCapBinarySequenceComparison X Y f Z U V k φ).comm₂₃.symm
  have hm : m ≫ F0.map (biprod.desc bu bv) =
      Fp.map (biprod.desc ru rv) ≫ i1_globalEvenCapExtendedMap X Y f Z k φ :=
    i1_extendedBinaryComparison_desc (2 * k : ℕ) _ _ _ ru rv bu bv
      (i1_globalEvenCapExtendedMap_domain X Y f Z k φ U).symm
      (i1_globalEvenCapExtendedMap_domain X Y f Z k φ V).symm
  haveI : Epi (Fp.map S.g) :=
    (i1_rationalChainSequence_extend_shortExact S
      (i1_relativeDomainBinarySequence_shortExact X Z (f ⁻¹' U) (f ⁻¹' V)) (2 * k : ℕ)).epi_g
  apply (cancel_epi (Fp.map S.g)).mp
  change Fp.map S.g ≫ (Fp.map asrc ≫ i1_globalEvenCapExtendedMap X Y f Z k φ) =
    Fp.map S.g ≫ (r ≫ F0.map atgt)
  rw [← Category.assoc, hs, ← hm, ← ht, ← Category.assoc, ← hc, Category.assoc]

end HodgeLean.Foundations.BundleResolution
